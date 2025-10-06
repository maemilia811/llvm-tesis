//===-- X86TypeSys.cpp - X86 Type System Analysis Implementation ----------===//
//
// This file implements a type system analysis for the X86 target in LLVM.
// It propagates and unifies type information (type_sys) for variables and
// instructions, tracking security levels (L/H) for both non-secret and secret
// data. The analysis is performed over LLVM IR instructions, basic blocks,
// functions, and modules.
//
//===----------------------------------------------------------------------===//

#include "llvm/IR/Instructions.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/SparseBitVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/CodeGen/MachineInstrBundle.h"
#include "llvm/CodeGen/MachineBasicBlock.h"
#include "llvm/CodeGen/MachineConstantPool.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineInstr.h"
#include "llvm/CodeGen/MachineInstrBuilder.h"
#include "llvm/CodeGen/MachineModuleInfo.h"
#include "llvm/CodeGen/MachineOperand.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/MachineSSAUpdater.h"
#include "llvm/CodeGen/TargetInstrInfo.h"
#include "llvm/CodeGen/TargetRegisterInfo.h"
#include "llvm/CodeGen/TargetSchedule.h"
#include "llvm/CodeGen/TargetSubtargetInfo.h"
#include "llvm/CodeGen/Passes.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/MC/MCSchedule.h"
#include "llvm/InitializePasses.h"
#include "llvm/Pass.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include <algorithm>
#include <cassert>
#include <iterator>
#include <iostream>
#include <optional>
#include <utility>
#include <map>
#include <stdexcept>
#include "llvm/IR/ModuleSlotTracker.h"
#include "llvm/IR/Instructions.h" // For llvm::BlockAddress
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h" // For llvm::BlockAddress
#include "DfenceTypeSys.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/GlobalVariable.h" // también necesario si iterás sobre GlobalVariable


using namespace llvm;

#define DEBUG_TYPE "x86-dfence-ts"

char ::DfenceTypeSys::ID = 0;

// FunctionPass *llvm::createDfenceTypeSystemPass() {
//     return new DfenceTypeSys();
// }

// Cache for gamma maps per basic block to avoid recomputation
std::map<BasicBlock*, std::map<std::string, type_sys>> gamma_cache;
std::map<std::string, std::map<std::string,type_sys>> gamma_fun;
llvm::Function *Fun = nullptr;

std::string getStableId(const llvm::Value *V) {
    std::string out;
    llvm::raw_string_ostream rso(out);
    V->printAsOperand(rso, false);
    return rso.str();
}

// Unifies two type_sys objects, propagating the highest (most secret) level
type_sys llvm::unify_typs(type_sys t1, type_sys t2) {
    if (t1 == N ) {
        return t2;
    } else {
        return t1;
    }
}

// Unifies two gamma maps by unifying their type_sys values for each key
std::map<std::string, type_sys> llvm::unify_maps(std::map<std::string, type_sys> m1, std::map<std::string, type_sys> m2) {
    std::map<std::string, type_sys> result;
    for (const auto& [key, value] : m1) {
        if (m2.find(key) != m2.end()) {
            result[key] = ::unify_typs(value, m2[key]);
        } else {
            result[key] = value;
        }
    }
    for (const auto& [key, value] : m2) {
        if (result.find(key) == result.end()) {
            result[key] = value;
        }
    }
    return result;
}

// Gets the type_sys for a given LLVM Value using the current gamma map
type_sys llvm::get_type_operand (const llvm::Value &v, std::map<std::string, type_sys> &gamma) {
    type_sys result;
    if (isa<Constant>(v)){
        result = N;
    }
    else {
        auto it = gamma.find(getStableId(&v));
        if (it != gamma.end()) {
            result = it->second;
        }
    }
    return result;
}

// Propagates and updates the gamma map for a single instruction
std::map<std::string, type_sys> llvm::get_gamma_instruction (const llvm::Instruction &I, std::map<std::string, type_sys> &gamma) {
    type_sys result;
    // Declare all variables that may be used in any case before the switch
    Value *op = nullptr;
    Value *op0 = nullptr;
    Value *op1 = nullptr;
    Value *op2 = nullptr;
    const Value *addr = nullptr;
    BasicBlock *n_lbl = nullptr;
    BasicBlock *exc_lbl = nullptr;
    type_sys t1, t2, t3, t;
    std::map<std::string, type_sys> gamma2, gamma3, gamma4;
    BasicBlock *defaultDest = nullptr;
    BasicBlock *bb = nullptr;
    BasicBlock *bb1 = nullptr;
    BasicBlock *bb2 = nullptr;
    const CallBrInst *CB = nullptr;
    const IndirectBrInst *IB = nullptr;
    std::map<std::string, type_sys>::iterator it = gamma.end();
    std::map<std::string, std::map<std::string, type_sys>>::iterator it_fun = gamma_fun.end();
    // Handle each instruction opcode and update gamma accordingly
    switch(I.getOpcode()) {
        // Binary operations and comparisons
        case Instruction::Add:
        case Instruction::FAdd:
        case Instruction::Sub:
        case Instruction::FSub:
        case Instruction::Mul: 
        case Instruction::FMul:
        case Instruction::UDiv:
        case Instruction::SDiv:
        case Instruction::FDiv:
        case Instruction::URem:
        case Instruction::SRem:
        case Instruction::FRem:
        case Instruction::And:
        case Instruction::Or:
        case Instruction::Xor:
        case Instruction::Shl:
        case Instruction::LShr:
        case Instruction::AShr:
        case Instruction::ICmp:
            op0 = I.getOperand(0);
            op1 = I.getOperand(1);
            t1 = ::get_type_operand(*op0, gamma);
            t2 = ::get_type_operand(*op1, gamma);
            result = ::unify_typs(t1, t2);
            gamma[getStableId(llvm::dyn_cast<llvm::Value>(&I))] = result;
            break;
        // Unary and cast operations
        case Instruction::FNeg:
        case Instruction::ZExt:
        case Instruction::SExt:
        case Instruction::Trunc:
        case Instruction::PtrToInt:
        case Instruction::FPToUI:
        case Instruction::FPToSI:
        case Instruction::UIToFP:
        case Instruction::SIToFP:
        case Instruction::FPTrunc:
        case Instruction::FPExt:
        case Instruction::BitCast:
        case Instruction::AddrSpaceCast:
        case Instruction::IntToPtr:
            op = I.getOperand(0);
            result = ::get_type_operand(*op, gamma);
            gamma[getStableId(llvm::dyn_cast<llvm::Value>(&I))] = result;
            break;
        // Select operation
        case Instruction::Select:
            op0 = I.getOperand(0);
            op1 = I.getOperand(1);
            op2 = I.getOperand(2);
            t1 = ::get_type_operand(*op0, gamma);
            if (!t1 == N) {
                if (const DebugLoc &DL = I.getDebugLoc()) {
                    DL.print(errs()); 
                    errs() << " A secret may leak through a select operation\n";
                } else {
                    errs() << "A secret may leak through a select operation\n";
                }
            }
            t2 = ::get_type_operand(*op1, gamma);
            t3 = ::get_type_operand(*op2, gamma);
            result = ::unify_typs(::unify_typs(t1, t2), t3);
            gamma[getStableId(llvm::dyn_cast<llvm::Value>(&I))] = result;
            break;
        // GetElementPtr operation
        case Instruction::GetElementPtr:
			op0 = I.getOperand(0);
            result = ::get_type_operand(*op0, gamma);
            for (unsigned i = 1; i < I.getNumOperands(); ++i) {
                op = I.getOperand(i);
                t = ::get_type_operand(*op, gamma);
				result = ::unify_typs(result, t);

            }
            gamma[getStableId(llvm::dyn_cast<llvm::Value>(&I))] = result;
            break;
        // Load operation
        case Instruction::Load:
            op = I.getOperand(0);
            t = ::get_type_operand(*op, gamma);
            if ( t == S ){
                if (const DebugLoc &DL = I.getDebugLoc()) {
                    DL.print(errs()); 
                    errs() << " A secret might leak by loading at this ptr address\n";
                } else {
                    errs() << "A secret might leak by loading at this ptr address\n";
                }
            }
            gamma[getStableId(llvm::dyn_cast<llvm::Value>(&I))] = S;
            break;
        // Store operation
        case Instruction::Store:
            op0 = I.getOperand(0);
            t1 = ::get_type_operand(*op0, gamma);
			op1 = I.getOperand(1);
			t2 = ::get_type_operand(*op1, gamma);
			if (t2 == S){
				if (const DebugLoc &DL = I.getDebugLoc()) {
                    DL.print(errs()); 
                    errs() << " A secret might leak by storing at this ptr address\n";
                } else {
                    errs() << "A secret might leak by storing at this ptr address\n";
                } 
			}
            break;
        // AtomicCmpXchg operation
        case Instruction::AtomicCmpXchg:
            op1 = I.getOperand(1);
            op2 = I.getOperand(2);
            t1 = ::get_type_operand(*op1, gamma);
            t2 = ::get_type_operand(*op2, gamma);
            result = ::unify_typs(t1, t2);
            op = I.getOperand(0);
			t = ::get_type_operand(*op, gamma);
			if (t == S){
				if (const DebugLoc &DL = I.getDebugLoc()) {
                    DL.print(errs()); 
                    errs() << " A secret might leak with CmpXchg at this ptr address\n";
                } else {
                    errs() << "A secret might leak with CmpXchg at this ptr address\n";
                }
			}
            break;
        // AtomicRMW operation
        case Instruction::AtomicRMW:
            op = I.getOperand(0);
            op1 = I.getOperand(1);
            t1 = ::get_type_operand(*op, gamma);
            t2 = ::get_type_operand(*op1, gamma);
            if (t1 == S){
				if (const DebugLoc &DL = I.getDebugLoc()) {
                    DL.print(errs()); 
                    errs() << " A secret might leak by doing an atomicrmw at this ptr address\n";
                } else {
                    errs() << "A secret might leak by doing an atomicrmw at this ptr address\n";
                }
			}
            gamma[getStableId(llvm::dyn_cast<llvm::Value>(&I))] = S;
            break;
        // Alloca operation
        case Instruction::Alloca:
            gamma[getStableId(llvm::dyn_cast<llvm::Value>(&I))] = N;
            break;
        // Fence operation
        case Instruction::Fence:
            for (auto &x : gamma){
                x.second = N;
            }
            break;
        // Dfence operation
        case Instruction::Dfence:
            op = I.getOperand(0);
            result = ::get_type_operand(*op, gamma);
            gamma[getStableId(llvm::dyn_cast<llvm::Value>(&I))] = N;
            break;
        // Call instruction
        case Instruction::Call:
            gamma2 = gamma;
            if (auto *IC = llvm::dyn_cast<CallInst>(&I))
            {
                it_fun = gamma_fun.find(IC->getCalledFunction()->getName().str());
                if (it_fun != gamma_fun.end()) {
                    gamma2 = it_fun->second;
                }
                else {
                    gamma2 = ::get_gamma_fun(* IC->getCalledFunction(), gamma2);
                }
                result = gamma2[IC->getCalledFunction()->getName().str()];
                gamma[getStableId(llvm::dyn_cast<llvm::Value>(&I))] = result;
            }
            break;
        // PHI node
        case Instruction::PHI:
            result = N;
            for (unsigned i = 0; i < I.getNumOperands(); i += 2) {
                Value *val = I.getOperand(i);
                result = ::unify_typs(result, ::get_type_operand(*val, gamma));
            }
            gamma[getStableId(llvm::dyn_cast<llvm::Value>(&I))] = result;
            break;
        // Ret instruction (not safe)
        /*case Instruction::Ret:
            if (const DebugLoc &DL = I.getDebugLoc()) {
                    errs() << "Erreur de typage à ";
                    DL.print(errs()); 
                    errs() << "A secret may leak through a select operation";
                } else {
                    errs() << "Erreur de typage : pas de debug info\n";
                } ("Return instruction encountered, a return instruction is not safe.");
            break;*/
        // Sret instruction
        case Instruction::Ret:
            if (I.getNumOperands() > 0) {
                op = I.getOperand(0);
                result = ::get_type_operand(*op, gamma);
            } else {
                result = N;
            }
            it = gamma.find(I.getParent()->getParent()->getName().str());
            if (it != gamma.end()) {
                result = ::unify_typs(result, it->second);
            }
            gamma[I.getParent()->getParent()->getName().str()] = result;
            break;
        // Branch instruction
        case Instruction::Br:
            if (I.getNumOperands() > 1) {
                op = I.getOperand(0);
                result = ::get_type_operand(*op, gamma);
                if (result == S) {
                    if (const DebugLoc &DL = I.getDebugLoc()) {
                        DL.print(errs()); 
                        errs() << " A secret may leak through a branch operation\n";
                    } else {
                        errs() << "A secret may leak through a branch operation\n";
                    } 
                }
                gamma2 = gamma;
                gamma3 = gamma;
                bb1 = I.getSuccessor(0);
                bb2 = I.getSuccessor(1);
                gamma2 = ::get_gamma_block(*bb1, gamma2);
                gamma3 = ::get_gamma_block(*bb2, gamma3);
                gamma = ::unify_maps(gamma2, gamma3);
            } else {
                bb = I.getSuccessor(0);
                gamma = ::get_gamma_block(*bb, gamma);
            }
            break;
        // Switch instruction
        case Instruction::Switch:
            gamma3 = gamma;
            for (unsigned i = 0; i < I.getNumOperands() - 1; i+=2) {
                op = I.getOperand(i);
                t = ::get_type_operand(*op, gamma);
                if (t == S) {
                    if (const DebugLoc &DL = I.getDebugLoc()) {
                        DL.print(errs()); 
                        errs() << " A secret may leak through a switch operation\n";
                    } else {
                        errs() << "A secret may leak through a switch operation\n";
                    } 
                }
                gamma2 = gamma;
                bb = llvm::dyn_cast<BasicBlock>(I.getOperand(i + 1));
                gamma2 = ::get_gamma_block(*bb, gamma2);
                gamma3 = ::unify_maps(gamma3, gamma2);
            }
            gamma = gamma3;
            break;
        // Invoke instruction
        case Instruction::Invoke:
            gamma2 = gamma;
            if (auto *In = llvm::dyn_cast<InvokeInst>(&I))
            {
                gamma2 = ::get_gamma_fun(* In->getCalledFunction(), gamma2);
                result = gamma2[In->getCalledFunction()->getName().str()];
                gamma[getStableId(llvm::dyn_cast<llvm::Value>(&I))] = result;
                n_lbl = In->getNormalDest();
                exc_lbl = In->getUnwindDest();
                gamma3 = gamma;
                gamma3 = ::get_gamma_block(*n_lbl, gamma3);
                gamma4 = gamma;
                gamma4 = ::get_gamma_block(*exc_lbl, gamma4);
                gamma = ::unify_maps(gamma3, gamma4);
            }
            break;
        // CallBr instruction
        case Instruction::CallBr:
            CB = llvm::dyn_cast<CallBrInst>(&I);
            defaultDest = CB->getDefaultDest();
            gamma2 = gamma;
            gamma2 = ::get_gamma_block(*defaultDest, gamma2);
            for (unsigned i = 0; i < CB->getNumIndirectDests(); ++i) {
                bb = CB->getIndirectDest(i);
                gamma3 = gamma;
                gamma3 = ::get_gamma_block(*bb, gamma3);
                gamma2 = ::unify_maps(gamma2, gamma3);
            }
            gamma = gamma2;
            break;
        // IndirectBr instruction
        case Instruction::IndirectBr:
            IB = llvm::dyn_cast<IndirectBrInst>(&I);
            addr = IB->getAddress();
			t = ::get_type_operand(*addr, gamma);
			if (t == S) {
				if (const DebugLoc &DL = I.getDebugLoc()) {
                    DL.print(errs()); 
                    errs() << " A secret might leak while jumping to this ptr\n";
                } else {
                    errs() << "A secret might leak while jumping to this ptr\n";
                } 
			}
            if (auto *BA = dyn_cast<BlockAddress>(addr)) {
                bb = BA->getBasicBlock();
                gamma = ::get_gamma_block(*bb, gamma);
            } else {
                if (const DebugLoc &DL = I.getDebugLoc()) {
                    DL.print(errs()); 
                    errs() << " IndirectBr instruction requires a BlockAddress operand\n";
                } else {
                    errs() << "IndirectBr instruction requires a BlockAddress operand\n";
                } 
            }
            break;
        // Default case: treat as non-secret unless it's a terminator
        default:
            errs() << "Unhandled instruction opcode: " << I.getOpcodeName() << "\n";
            result = N;
            if (I.isTerminator()) {
                break;
            }
            else {
                gamma[getStableId(llvm::dyn_cast<llvm::Value>(&I))] = result;
            }
            break;
    }
    return gamma;
}

// Propagates the gamma map through all instructions in a basic block
std::map<std::string, type_sys> llvm::get_gamma_block(const BasicBlock &BB, 
                                                std::map<std::string, type_sys> &gamma) {
    // Check if the gamma for this block is already cached
    auto it = gamma_cache.find(const_cast<BasicBlock*>(&BB));
    if (it != gamma_cache.end()) {
        return it->second;
    }
    for (const Instruction &I : BB) {
        if (I.isTerminator()) {
            gamma_cache[const_cast<BasicBlock*>(&BB)] = gamma;
        }
        gamma = ::get_gamma_instruction(I, gamma);
    }
    // Cache the gamma for the block
    gamma_cache[const_cast<BasicBlock*>(&BB)] = gamma;
    return gamma;
}

// Propagates the gamma map through all basic blocks in a function
std::map<std::string, type_sys> llvm::get_gamma_fun(const Function &F, 
                                              std::map<std::string, type_sys> &gamma) {
    auto it = gamma_fun.find(F.getName().str());
    if (it != gamma_fun.end()) {
        return it->second;
    }
    Fun = const_cast<Function*>(&F);
    for (const llvm::Argument &Arg : F.args()) {
        gamma[getStableId(&Arg)] = S;
    }
    gamma[F.getName().str()] = N;
    gamma_fun[F.getName().str()] = gamma;
    for (const BasicBlock &BB : F) {
        gamma = ::get_gamma_block(BB, gamma);
        gamma_fun[F.getName().str()] = gamma;
    }
    return gamma;
}

// Initializes gamma for globals and propagates through all functions in a module
std::map<std::string, type_sys> llvm::get_gamma_module(const Module &M) {
    std::map<std::string, type_sys> gamma;
    for (auto &GV : M.globals()) {
        StringRef name = GV.getName();
        if (!name.empty()) {
            type_sys t = N;
            gamma[name.str()] = t;
        }
    }
    for (const Function &F : M) {
        if (!F.isDeclaration()) {
            gamma = ::get_gamma_fun(F, gamma);
        }
    }
    return gamma;
}


bool DfenceTypeSys::runOnMachineFunction(MachineFunction &MF) {
    Function &F = MF.getFunction();
    Module *M = F.getParent();
    std::map<std::string,type_sys> gamma = ::get_gamma_module(*M);
    return true;
}

