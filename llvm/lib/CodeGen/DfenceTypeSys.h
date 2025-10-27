//===-- DfenceTypeSys.h - X86 Dfence Type System Analysis -------*- C++ -*-===//
//
// This header declares the DfenceTypeSys pass and related helper functions
// used to perform type system analysis on the X86 target. It tracks the
// propagation of type_sys (security levels) through LLVM IR instructions,
// basic blocks, functions, and modules.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_LIB_TARGET_X86_DFENCETYPESYS_H
#define LLVM_LIB_TARGET_X86_DFENCETYPESYS_H

#include "llvm/Pass.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Module.h"
#include <map>
#include <string>

namespace llvm {

//===----------------------------------------------------------------------===//
//  Type System Definitions
//===----------------------------------------------------------------------===//

/// Security type for data values.
enum type_sys {
    N,  ///< Non-secret (normal) data
    S   ///< Secret data
};

//===----------------------------------------------------------------------===//
//  Type System Helper Functions
//===----------------------------------------------------------------------===//

/// Returns a unique and stable identifier for an LLVM Value.
std::string getStableId(const llvm::Value *V);

/// Unify two type_sys values (propagating the highest secrecy level).
type_sys unify_typs(type_sys t1, type_sys t2);

/// Unify two gamma maps (mapping identifiers to type_sys).
std::map<std::string, type_sys>
unify_maps(std::map<std::string, type_sys> m1,
           std::map<std::string, type_sys> m2);

/// Retrieve the type_sys associated with a given operand.
type_sys get_type_operand(const llvm::Value &v,
                          std::map<std::string, type_sys> &gamma);

/// Propagate and update the gamma map for a single instruction.
std::map<std::string, type_sys>
get_gamma_instruction(const llvm::Instruction &I,
                      std::map<std::string, type_sys> &gamma);

/// Propagate the gamma map through all instructions in a basic block.
std::map<std::string, type_sys>
get_gamma_block(const llvm::BasicBlock &BB,
                std::map<std::string, type_sys> &gamma);

/// Propagate the gamma map through all basic blocks in a function.
std::map<std::string, type_sys>
get_gamma_fun(const llvm::Function &F,
              std::map<std::string, type_sys> &gamma);

/// Initialize gamma for globals and propagate through all functions in a module.
std::map<std::string, type_sys>
get_gamma_module(const llvm::Module &M);

//===----------------------------------------------------------------------===//
//  DfenceTypeSys Pass
//===----------------------------------------------------------------------===//

/// Machine-level analysis pass that applies the type system propagation
/// to detect possible secret-dependent data flows.
class DfenceTypeSys : public llvm::MachineFunctionPass {
public:
    static char ID;

    DfenceTypeSys() : MachineFunctionPass(ID) {}

    /// Run the Dfence type system analysis on a machine function.
    bool runOnMachineFunction(llvm::MachineFunction &MF) override;

    llvm::StringRef getPassName() const override {
        return "X86 Dfence Type System Analysis";
    }
};

//===----------------------------------------------------------------------===//
//  Pass Creation Function (optional, if used by LLVM’s PassRegistry)
//===----------------------------------------------------------------------===//

// llvm::FunctionPass *createDfenceTypeSystemPass();

} // end namespace llvm

#endif // LLVM_LIB_TARGET_X86_DFENCETYPESYS_H
