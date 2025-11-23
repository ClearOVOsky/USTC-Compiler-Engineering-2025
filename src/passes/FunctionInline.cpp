#include "../../include/passes/FunctionInline.hpp"
#include "../../include/lightir/Function.hpp"

#include "BasicBlock.hpp"
#include "Instruction.hpp"
#include "Value.hpp"
#include "Constant.hpp"
#include "logging.hpp"
#include <cassert>
#include <utility>
#include <vector>
#include <set>
#include <map>

void FunctionInline::run() { inline_all_functions(); }

void FunctionInline::inline_all_functions() {
    
    std::set<Function *> recursive_func;
    for (auto &func : m_->get_functions()) {
        for (auto &bb : func.get_basic_blocks()) {
            for (auto &inst : bb.get_instructions()) {
                if (inst.is_call()) {
                    auto call = &inst;
                    auto func1 = static_cast<Function *>(call->get_operand(0));
                    if (func1 == &func) {
                        recursive_func.insert(func1);
                        break;
                    }
                }
            }
        }
    }
    for (auto &func : m_->get_functions()) {
        if (outside_func.find(func.get_name()) != outside_func.end()) {
            continue;
        }
    a1:
        for (auto &bb : func.get_basic_blocks()) {
            for (auto &inst : bb.get_instructions()) {
                if (inst.is_call()) {
                    auto call = &inst;
                    auto func1 = static_cast<Function *>(call->get_operand(0));
                    if (func1 == &func) {
                        continue;
                    }
                    if (recursive_func.find(func1) != recursive_func.end())
                        continue;
                    if (outside_func.find(func1->get_name()) !=
                        outside_func.end())
                        continue;
                    if(func1->get_basic_blocks().size() >=6){
                        continue;
                    }
                    inline_function(call, func1);
                    goto a1;
                }
            }
        }
    }
}

void FunctionInline::inline_function(Instruction *call, Function *origin) {
    std::map<Value *, Value *> v_map;
    std::vector<BasicBlock *> bb_list;
    std::vector<Instruction *> ret_list;
    for (auto &arg : origin->get_args()) {
        v_map.insert(std::make_pair(static_cast<Value *>(&arg),
                                    call->get_operand(arg.get_arg_no() + 1)));
    }
    auto call_bb = call->get_parent();
    auto call_func = call_bb->get_parent();
    std::vector<BasicBlock *> ret_void_bbs;
    for (auto &bb : origin->get_basic_blocks()) {
        auto bb_new =
            BasicBlock::create(call_func->get_parent(), "", call_func);
        v_map.insert(std::make_pair(static_cast<Value *>(&bb),
                                    static_cast<Value *>(bb_new)));
        bb_list.push_back(bb_new);
        for (auto &inst : bb.get_instructions()) {
            if (inst.is_ret() && origin->get_return_type()->is_void_type()) {
                ret_void_bbs.push_back(bb_new);
                continue;
            }
            
            Instruction *inst_new ;
            if (inst.is_call()) {
                auto call = static_cast<CallInst *>(&inst);
                auto func = static_cast<Function *>(call->get_operand(0));
                inst_new = new CallInst(func, {call->get_operands().begin() + 1, call->get_operands().end()}, bb_new);
            }
            else {
                inst_new = inst.clone(bb_new);
                if (inst.is_phi()) {
                    bb_new->remove_instr(inst_new);
                    bb_new->add_instr_begin(inst_new);
                    for (int i = (int)inst_new->get_num_operand() - 2; i >= 0; i -= 2) {
                        auto val_op = inst_new->get_operand(i);
                        auto bb_op = (i + 1 < (int)inst_new->get_num_operand()) ? inst_new->get_operand(i + 1) : nullptr;
                        if (val_op == nullptr || bb_op == nullptr) {
                            if (i + 1 < (int)inst_new->get_num_operand()) {
                                inst_new->remove_operand(i + 1);
                            }
                            inst_new->remove_operand(i);
                        }
                    }
                }
            }
            v_map.insert(std::make_pair(static_cast<Value *>(&inst),
                                        static_cast<Value *>(inst_new)));
            if (inst.is_ret()) {
                ret_list.push_back(inst_new);
            }
        }
    }
    for (auto bb : bb_list) {
        for (auto &inst : bb->get_instructions()) {
            if (inst.is_phi()) {
                for (unsigned i = 0; i < inst.get_num_operand(); i++) {
                    auto op = inst.get_operand(i);
                    if (op != nullptr && v_map.find(op) != v_map.end()) {
                        auto mapped = v_map[op];
                        if (mapped != nullptr) {
                            inst.set_operand(i, mapped);
                        } else {
                            inst.set_operand(i, nullptr);
                        }
                    }
                }
                std::vector<int> to_remove;
                auto pre_bbs = bb->get_pre_basic_blocks();
                for (int i = 0; i < (int)inst.get_num_operand(); i += 2) {
                    auto val_op = inst.get_operand(i);
                    auto bb_op = (i + 1 < (int)inst.get_num_operand()) ? inst.get_operand(i + 1) : nullptr;
                    bool should_remove = false;
                    if (val_op == nullptr || bb_op == nullptr) {
                        should_remove = true;
                    } else {
                        auto bb_operand = dynamic_cast<BasicBlock *>(bb_op);
                        if (bb_operand == nullptr || std::find(pre_bbs.begin(), pre_bbs.end(), bb_operand) == pre_bbs.end()) {
                            should_remove = true;
                        }
                    }
                    if (should_remove) {
                        to_remove.push_back(i);
                    }
                }
                for (int i = to_remove.size() - 1; i >= 0; i--) {
                    int idx = to_remove[i];
                    if (idx + 1 < (int)inst.get_num_operand()) {
                        inst.remove_operand(idx + 1);
                    }
                    inst.remove_operand(idx);
                }
            } else {
                for (unsigned i = 0; i < inst.get_num_operand(); i++) {
                    auto op = inst.get_operand(i);
                    if (op != nullptr && v_map.find(op) != v_map.end()) {
                        auto mapped_op = v_map[op];
                        if (mapped_op != nullptr) {
                            inst.set_operand(i, mapped_op);
                        }
                    }
                }
            }
        }
    }
    Value *ret_val = nullptr;
    bool is_terminated = false;
    auto bb_new = BasicBlock::create(call_func->get_parent(), "", call_func);
    if (!origin->get_return_type()->is_void_type()) {
        if (ret_list.size() == 1) {
            auto ret = ret_list.front();
            ret_val = ret->get_operand(0);
            auto ret_bb = ret->get_parent();
            ret_bb->remove_instr(ret);
            BranchInst::create_br(bb_new, ret_bb);
        } else {
            auto bb_phi = BasicBlock::create(call_func->get_parent(), "", call_func);
            std::vector<std::pair<Value *, BasicBlock *>> ret_pairs;
            for (auto ret : ret_list) {
                auto ret_bb = ret->get_parent();
                assert(ret_bb != nullptr && "Return instruction should have a parent basic block");
                
                Value *ret_val = nullptr;
                if (ret->get_num_operand() > 0) {
                    ret_val = ret->get_operand(0);
                    if (v_map.find(ret_val) != v_map.end()) {
                        ret_val = v_map[ret_val];
                    }
                }
                if (ret_val == nullptr) {
                    ret_val = ConstantZero::get(origin->get_return_type(), call_func->get_parent());
                }
                ret_pairs.push_back({ret_val, ret_bb});
                ret_bb->remove_instr(ret);
                BranchInst::create_br(bb_phi, ret_bb);
            }
            
            auto phi = PhiInst::create_phi(origin->get_return_type(), bb_phi);
            for (auto &pair : ret_pairs) {
                Value *val = pair.first;
                if (val == nullptr) {
                    val = ConstantZero::get(origin->get_return_type(), call_func->get_parent());
                }
                BasicBlock *bb = pair.second;
                assert(bb != nullptr && "Basic block should not be nullptr");
                if (val == nullptr) {
                    val = ConstantZero::get(origin->get_return_type(), call_func->get_parent());
                }
                phi->add_phi_pair_operand(val, bb);
            }
            
            bb_phi->add_instr_begin(phi);
            ret_val = phi;
            bb_list.push_back(bb_phi);
            BranchInst::create_br(bb_new, bb_phi);
        }
    } else {
        assert(ret_void_bbs.size() > 0);
        for (auto bb : ret_void_bbs) {
            BranchInst::create_br(bb_new, bb);
        }
    }
    std::vector<Instruction *> del_list;
    BranchInst* br = nullptr;
    Instruction* original_terminator = nullptr;
    BasicBlock* original_target = nullptr;
    for (auto &inst : call_bb->get_instructions()) {
        if (!is_terminated) {
            if (&(inst) == call) {
                if (call_bb->is_terminated()) {
                    auto terminator = call_bb->get_terminator();
                    if (terminator->is_br()) {
                        auto br_inst = static_cast<BranchInst*>(terminator);
                        original_target = static_cast<BasicBlock*>(br_inst->get_operand(0));
                    }
                    call_bb->remove_instr(terminator);
                }
                br = BranchInst::create_br(bb_list.front(), call_bb);
                if (!origin->get_return_type()->is_void_type()) {
                    call->replace_all_use_with(ret_val);
                }
                is_terminated = true;
            }
        } else {
            if(dynamic_cast<BranchInst*>(&inst) == br){
                continue;
            }
            if (inst.isTerminator()) {
                if (inst.is_br()) {
                    auto br_inst = static_cast<BranchInst*>(&inst);
                    original_target = static_cast<BasicBlock*>(br_inst->get_operand(0));
                }
                del_list.push_back(&inst);
            } else {
                del_list.push_back(&inst);
            }
        }
    }
    call_bb->remove_instr(call);
    origin->remove_use(call, 0);
    
    for (auto inst : del_list) {
        call_bb->remove_instr(inst);
        if (inst->isTerminator()) {
                if (inst->is_br()) {
                    auto br_inst = static_cast<BranchInst*>(inst);
                    auto target_bb = static_cast<BasicBlock*>(br_inst->get_operand(0));
                    BranchInst::create_br(target_bb, bb_new);
                } else if (inst->is_ret()) {
                    bb_new->add_instruction(inst);
                    inst->set_parent(bb_new);
                }
        } else {
            bb_new->add_instruction(inst);
            inst->set_parent(bb_new);
        }
    }
    
    if (!bb_new->is_terminated()) {
        if (original_target != nullptr && original_target->get_parent() == call_func) {
            BranchInst::create_br(original_target, bb_new);
        } else {
            if (call_func->get_return_type()->is_void_type()) {
                ReturnInst::create_void_ret(bb_new);
            } else if (call_func->get_return_type()->is_integer_type()) {
                auto zero = ConstantInt::get(0, call_func->get_parent());
                ReturnInst::create_ret(zero, bb_new);
            } else if (call_func->get_return_type()->is_float_type()) {
                auto zero = ConstantFP::get(0.0f, call_func->get_parent());
                ReturnInst::create_ret(zero, bb_new);
            } else {
                auto zero = ConstantZero::get(call_func->get_return_type(), call_func->get_parent());
                ReturnInst::create_ret(zero, bb_new);
            }
        }
    }

    origin->reset_bbs();
    call_func->reset_bbs();
    
    std::set<BasicBlock *> all_bbs_set;
    for (auto bb : bb_list) {
        all_bbs_set.insert(bb);
    }
    all_bbs_set.insert(bb_new);
    for (auto &bb : call_func->get_basic_blocks()) {
        all_bbs_set.insert(&bb);
    }
    
    for (auto bb : all_bbs_set) {
        for (auto &inst : bb->get_instructions()) {
            if (inst.is_phi()) {
                auto phi_inst = static_cast<PhiInst *>(&inst);
                auto pre_bbs = bb->get_pre_basic_blocks();
                std::map<BasicBlock *, Value *> phi_map;
                for (int i = 0; i < (int)inst.get_num_operand(); i += 2) {
                    if (i + 1 < (int)inst.get_num_operand()) {
                        auto val_op = inst.get_operand(i);
                        auto bb_op = inst.get_operand(i + 1);
                        if (val_op != nullptr && bb_op != nullptr) {
                            auto bb_operand = dynamic_cast<BasicBlock *>(bb_op);
                            if (bb_operand != nullptr) {
                                phi_map[bb_operand] = val_op;
                            }
                        }
                    }
                }
                
                while (inst.get_num_operand() > 0) {
                    inst.remove_operand(0);
                }
                
                auto phi_type = inst.get_type();
                for (auto pre_bb : pre_bbs) {
                    Value *val = nullptr;
                    if (phi_map.find(pre_bb) != phi_map.end()) {
                        val = phi_map[pre_bb];
                    } else {
                        if (phi_type->is_integer_type()) {
                            val = ConstantInt::get(0, call_func->get_parent());
                        } else if (phi_type->is_float_type()) {
                            val = ConstantFP::get(0.0f, call_func->get_parent());
                        } else {
                            val = ConstantZero::get(phi_type, call_func->get_parent());
                        }
                    }
                    phi_inst->add_phi_pair_operand(val, pre_bb);
                }
            }
        }
    }
    
    return;
}