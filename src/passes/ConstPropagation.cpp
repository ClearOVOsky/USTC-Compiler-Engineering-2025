#include "ConstPropagation.hpp"

#include "Instruction.hpp"
#include "logging.hpp"

ConstantInt *ConstFolder::compute(Instruction::OpID op, ConstantInt *value1, ConstantInt *value2) {
    int c_value1 = value1->get_value();
    int c_value2 = value2->get_value();

    switch (op) {
    case Instruction::add:
        return ConstantInt::get(c_value1 + c_value2, module_);
        break;
    case Instruction::sub:
        return ConstantInt::get(c_value1 - c_value2, module_);
        break;
    case Instruction::mul:
        return ConstantInt::get(c_value1 * c_value2, module_);
        break;
    case Instruction::sdiv:
        return ConstantInt::get(static_cast<int>(c_value1 / c_value2), module_);
        break;
    case Instruction::eq:
        return ConstantInt::get(c_value1 == c_value2, module_);
        break;
    case Instruction::ne:
        return ConstantInt::get(c_value1 != c_value2, module_);
        break;
    case Instruction::gt:
        return ConstantInt::get(c_value1 > c_value2, module_);
        break;
    case Instruction::ge:
        return ConstantInt::get(c_value1 >= c_value2, module_);
        break;
    case Instruction::lt:
        return ConstantInt::get(c_value1 < c_value2, module_);
        break;
    case Instruction::le:
        return ConstantInt::get(c_value1 <= c_value2, module_);
        break;
    default:
        return nullptr;
        break;
    }
}

ConstantFP *ConstFolder::compute(Instruction::OpID op, ConstantFP *value1, ConstantFP *value2) {
    float c_value1 = value1->get_value();
    float c_value2 = value2->get_value();
    switch (op) {
    case Instruction::fadd:
        return ConstantFP::get(c_value1 + c_value2, module_);
        break;
    case Instruction::fsub:
        return ConstantFP::get(c_value1 - c_value2, module_);
        break;
    case Instruction::fmul:
        return ConstantFP::get(c_value1 * c_value2, module_);
        break;
    case Instruction::fdiv:
        return ConstantFP::get(c_value1 / c_value2, module_);
        break;
    // Float comparison returns i1, handled separately
    case Instruction::feq:
    case Instruction::fne:
    case Instruction::fgt:
    case Instruction::fge:
    case Instruction::flt:
    case Instruction::fle:
        return nullptr;
        break;
    default:
        return nullptr;
        break;
    }
}
ConstantFP *ConstFolder::compute(Instruction::OpID op, ConstantInt *value1) {
    int c_value1 = value1->get_value();

    switch (op) {
    case Instruction::sitofp:
        return ConstantFP::get((float) c_value1, module_);
        break;

    default:
        return nullptr;
        break;
    }
}

ConstantInt *ConstFolder::compute(Instruction::OpID op, ConstantFP *value1) {
    float c_value1 = value1->get_value();
    switch (op) {
    case Instruction::fptosi:
        return ConstantInt::get(static_cast<int>(c_value1), module_);
        break;

    default:
        return nullptr;
        break;
    }
}

ConstantFP *cast_constantfp(Value *value) {
    auto constant_fp_ptr = dynamic_cast<ConstantFP *>(value);
    if (constant_fp_ptr) {
        return constant_fp_ptr;
    }
    return nullptr;
}
ConstantInt *cast_constantint(Value *value) {
    auto constant_int_ptr = dynamic_cast<ConstantInt *>(value);
    if (constant_int_ptr) {
        return constant_int_ptr;
    }
    return nullptr;
}

void ConstPropagation::run() {
    bool changed = true;
    while (changed) {
        changed = false;
        for (auto &func : m_->get_functions()) {
            localvar_def.clear();
            
            for (auto &bb : func.get_basic_blocks()) {
                wait_delete.clear();

                for (auto &instr : bb.get_instructions()) {
                    if (instr.is_store()) {
                        auto store_ins = static_cast<StoreInst *>(&instr);
                        auto lval = store_ins->get_lval();
                        auto rval = store_ins->get_rval();
                        
                        Constant *const_val = nullptr;
                        if (auto const_int = cast_constantint(rval)) {
                            const_val = const_int;
                        } else if (auto const_fp = cast_constantfp(rval)) {
                            const_val = const_fp;
                        }
                        
                        if (auto global_var = dynamic_cast<GlobalVariable *>(lval)) {
                            auto global_type = global_var->get_type();
                            if (global_type->is_pointer_type()) {
                                auto element_type = global_type->get_pointer_element_type();
                                if (!element_type->is_array_type()) {
                                    if (const_val) {
                                        globalvar_def[global_var] = const_val;
                                    } else {
                                        globalvar_def.erase(global_var);
                                    }
                                }
                            } else {
                                if (const_val) {
                                    globalvar_def[global_var] = const_val;
                                } else {
                                    globalvar_def.erase(global_var);
                                }
                            }
                        }
                        else if (auto alloca_ins = dynamic_cast<AllocaInst *>(lval)) {
                            auto element_type = alloca_ins->get_alloca_type();
                            if (!element_type->is_array_type()) {
                                if (const_val) {
                                    localvar_def[alloca_ins] = const_val;
                                } else {
                                    localvar_def.erase(alloca_ins);
                                }
                            }
                        }
                        else if (auto gep_ins = dynamic_cast<GetElementPtrInst *>(lval)) {
                            auto base_ptr = gep_ins->get_operand(0);
                            if (auto global_var = dynamic_cast<GlobalVariable *>(base_ptr)) {
                                globalvar_def.erase(global_var);
                            }
                            else if (auto alloca_ins = dynamic_cast<AllocaInst *>(base_ptr)) {
                                localvar_def.erase(alloca_ins);
                            }
                        }
                    }
                    else if (instr.is_load()) {
                        auto load_ins = static_cast<LoadInst *>(&instr);
                        auto ptr = load_ins->get_lval();
                        
                        Constant *const_val = nullptr;
                        
                        if (auto global_var = dynamic_cast<GlobalVariable *>(ptr)) {
                            auto global_type = global_var->get_type();
                            if (global_type->is_pointer_type()) {
                                auto element_type = global_type->get_pointer_element_type();
                                if (!element_type->is_array_type()) {
                                    if (globalvar_def.find(global_var) != globalvar_def.end()) {
                                        const_val = globalvar_def[global_var];
                                    }
                                }
                            } else {
                                if (globalvar_def.find(global_var) != globalvar_def.end()) {
                                    const_val = globalvar_def[global_var];
                                }
                            }
                        }
                        else if (auto alloca_ins = dynamic_cast<AllocaInst *>(ptr)) {
                            auto element_type = alloca_ins->get_alloca_type();
                            if (!element_type->is_array_type()) {
                                if (localvar_def.find(alloca_ins) != localvar_def.end()) {
                                    const_val = localvar_def[alloca_ins];
                                }
                            }
                        }
                        
                        if (const_val) {
                            instr.replace_all_use_with(const_val);
                            wait_delete.push_back(&instr);
                            changed = true;
                        }
                    }
                    if (instr.is_add() || instr.is_sub() || instr.is_mul() || instr.is_div()) {
                        if (instr.get_num_operand() < 2) {
                            continue;
                        }
                        auto value1 = cast_constantint(instr.get_operand(0));
                        auto value2 = cast_constantint(instr.get_operand(1));
                        if (value1 && value2) {
                            auto fold_const = folder->compute(instr.get_instr_type(), value1, value2);

                            instr.replace_all_use_with(fold_const);
                            wait_delete.push_back(&instr);
                            changed = true;
                        }
                    }
                    else if (instr.is_fadd() || instr.is_fsub() || instr.is_fmul() || instr.is_fdiv()) {
                        if (instr.get_num_operand() < 2) {
                            continue;
                        }
                        auto value1 = cast_constantfp(instr.get_operand(0));
                        auto value2 = cast_constantfp(instr.get_operand(1));
                        if (value1 && value2) {
                            auto fold_const = folder->compute(instr.get_instr_type(), value1, value2);
                            if (fold_const) {
                                instr.replace_all_use_with(fold_const);
                                wait_delete.push_back(&instr);
                                changed = true;
                            }
                        }
                    }
                    else if (instr.is_cmp()) {
                        if (instr.get_num_operand() < 2) {
                            continue;
                        }
                        auto value1 = cast_constantint(instr.get_operand(0));
                        auto value2 = cast_constantint(instr.get_operand(1));
                        if (value1 && value2) {
                            auto fold_const = folder->compute(instr.get_instr_type(), value1, value2);
                            if (fold_const) {
                                instr.replace_all_use_with(fold_const);
                                wait_delete.push_back(&instr);
                                changed = true;
                            }
                        }
                    }
                    else if (instr.is_fcmp()) {
                        if (instr.get_num_operand() < 2) {
                            continue;
                        }
                        auto value1 = cast_constantfp(instr.get_operand(0));
                        auto value2 = cast_constantfp(instr.get_operand(1));
                        if (value1 && value2) {
                            float c_value1 = value1->get_value();
                            float c_value2 = value2->get_value();
                            bool result = false;
                            switch (instr.get_instr_type()) {
                            case Instruction::feq:
                                result = c_value1 == c_value2;
                                break;
                            case Instruction::fne:
                                result = c_value1 != c_value2;
                                break;
                            case Instruction::fgt:
                                result = c_value1 > c_value2;
                                break;
                            case Instruction::fge:
                                result = c_value1 >= c_value2;
                                break;
                            case Instruction::flt:
                                result = c_value1 < c_value2;
                                break;
                            case Instruction::fle:
                                result = c_value1 <= c_value2;
                                break;
                            default:
                                break;
                            }
                            auto fold_const = ConstantInt::get(result, m_);
                            instr.replace_all_use_with(fold_const);
                            wait_delete.push_back(&instr);
                            changed = true;
                        }
                    }
                    else if (instr.is_si2fp()) {
                        if (instr.get_num_operand() < 1) {
                            continue;
                        }
                        auto value1 = cast_constantint(instr.get_operand(0));
                        if (value1) {
                            auto fold_const = folder->compute(instr.get_instr_type(), value1);
                            if (fold_const) {
                                instr.replace_all_use_with(fold_const);
                                wait_delete.push_back(&instr);
                                changed = true;
                            }
                        }
                    }
                    else if (instr.is_fp2si()) {
                        if (instr.get_num_operand() < 1) {
                            continue;
                        }
                        auto value1 = cast_constantfp(instr.get_operand(0));
                        if (value1) {
                            auto fold_const = folder->compute(instr.get_instr_type(), value1);
                            if (fold_const) {
                                instr.replace_all_use_with(fold_const);
                                wait_delete.push_back(&instr);
                                changed = true;
                            }
                        }
                    }
                }
                for (auto instr : wait_delete) {
                    bb.erase_instr(instr);
                }
            }
        }
    }
    
    globalvar_def.clear();

    for (auto &func : m_->get_functions()) {
        for (auto &bb : func.get_basic_blocks()) {
            builder->set_insert_point(&bb);
            auto it = bb.get_instructions().begin();
            while (it != bb.get_instructions().end()) {
                auto &instr = *it;
                ++it;
                if (instr.is_br()) {
                    auto br_inst = static_cast<BranchInst *>(&instr);
                    if (br_inst->is_cond_br()) {
                        if (br_inst->get_num_operand() < 3) {
                            continue;
                        }
                        auto cond = br_inst->get_condition();
                        auto const_cond = cast_constantint(cond);
                        if (const_cond) {
                            auto cond_value = const_cond->get_value();
                            BasicBlock *target_bb = nullptr;
                            BasicBlock *unused_bb = nullptr;
                            
                            if (cond_value != 0) {
                                target_bb = static_cast<BasicBlock *>(br_inst->get_operand(1));
                                unused_bb = static_cast<BasicBlock *>(br_inst->get_operand(2));
                            } else {
                                target_bb = static_cast<BasicBlock *>(br_inst->get_operand(2));
                                unused_bb = static_cast<BasicBlock *>(br_inst->get_operand(1));
                            }
                            
                            bb.erase_instr(&instr);
                            builder->create_br(target_bb);
                        }
                    }
                }
            }
        }
    }
}

bool ConstPropagation::is_entry(BasicBlock *bb) {
    auto func = bb->get_parent();
    if (func == nullptr) {
        return false;
    }
    return func->get_entry_block() == bb;
    
}

void ConstPropagation::clear_blocks_recs(BasicBlock *start_bb) {
    auto func = start_bb->get_parent();
    if (func == nullptr) {
        LOG(ERROR) << "basic block-" << start_bb->get_name() << " has no parent function";
    } else {
        auto prev_bb = start_bb->get_pre_basic_blocks();
        if (prev_bb.size() == 0 && !is_entry(start_bb)) {
            auto succ_bb = start_bb->get_succ_basic_blocks();
            func->remove(start_bb);
            for (auto each_succ_bb : succ_bb) {
                if (each_succ_bb->get_parent() == nullptr) {
                    continue;
                }
                std::vector<Instruction*> del_inst;
                for (auto &instr1 : each_succ_bb->get_instructions()) {
                    auto instr = &instr1;
                    if (instr->is_phi()) {
                        LOG(DEBUG) << "Find a PHI instruction in the sucess node of "
                                      "useless branch";
                        std::vector<int> indices_to_remove;
                        int num_operands = instr->get_num_operand();
                        for (int i = 1; i < num_operands; i += 2) {
                            if (i < instr->get_num_operand() && 
                                instr->get_operand(i) == start_bb) {
                                indices_to_remove.push_back(i);
                            }
                        }
                        // Remove in reverse order to avoid index shifting
                        // PHI format: [value0, bb0, value1, bb1, ...]
                        for (auto it = indices_to_remove.rbegin(); it != indices_to_remove.rend(); ++it) {
                            int i = *it;
                            int current_num_operands = instr->get_num_operand();
                            if (i >= 1 && i < current_num_operands && i - 1 < current_num_operands) {
                                LOG(DEBUG) << "remove unuseful phi branch in the index of " << i - 1
                                           << " and " << i;
                                instr->remove_operand(i);
                                if (i - 1 < instr->get_num_operand()) {
                                    instr->remove_operand(i - 1);
                                }
                            }
                        }
                        int operands_num_phi = instr->get_num_operand();
                        if (operands_num_phi == 2 && instr->get_num_operand() >= 1) {
                            auto value = instr->get_operand(0);
                            instr->replace_all_use_with(value);
                            del_inst.push_back(instr);
                        }
                    }
                }
                for(auto instr : del_inst) each_succ_bb->erase_instr(instr);
                if (each_succ_bb->get_parent() != nullptr) {
                    clear_blocks_recs(each_succ_bb);
                }
            }
        }
    }
}
