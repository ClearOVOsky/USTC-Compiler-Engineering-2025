#include "DeadCode.hpp"
#include "Instruction.hpp"
#include "logging.hpp"
#include <memory>
#include <vector>


// 处理流程：两趟处理，mark 标记有用变量，sweep 删除无用指令
void DeadCode::run() {
    bool changed{};
    func_info->run();
    do {
        changed = false;
        for (auto &F : m_->get_functions()) {
            auto func = &F;
            changed |= clear_basic_blocks(func);
            mark(func);
            changed |= sweep(func);
        }
    } while (changed);
    LOG_INFO << "dead code pass erased " << ins_count << " instructions";
}

bool DeadCode::clear_basic_blocks(Function *func) {
    bool changed = 0;
    std::vector<BasicBlock *> to_erase;
    for (auto &bb1 : func->get_basic_blocks()) {
        auto bb = &bb1;
        if(bb->get_pre_basic_blocks().empty() && bb != func->get_entry_block()) {
            to_erase.push_back(bb);
            changed = 1;
        }
    }
    for (auto &bb : to_erase) {
        bb->erase_from_parent();
        delete bb;
    }
    return changed;
}

void DeadCode::mark(Function *func) {
    // 初始化 marked 映射和 work_list
    marked.clear();
    work_list.clear();
    
    // 遍历所有基本块和指令，找到关键指令
    for (auto &bb : func->get_basic_blocks()) {
        for (auto &instr : bb.get_instructions()) {
            auto ins = &instr;
            if (is_critical(ins)) {
                mark(ins);
            }
        }
    }
    
    // 处理 work_list 
    while(!work_list.empty()) {
        auto ins = work_list.front();
        work_list.pop_front();
        
        // 遍历该指令的所有操作数
        for (auto op : ins->get_operands()) {
            if (auto op_ins = dynamic_cast<Instruction *>(op)) {
                // 如果操作数是指令且未被标记，则标记它
                if (marked.find(op_ins) == marked.end() || !marked[op_ins]) {
                    marked[op_ins] = true;
                    work_list.push_back(op_ins);
                }
            }
        }
    }
}

void DeadCode::mark(Instruction *ins) {
    // 如果指令已经被标记，返回
    if (marked.find(ins) != marked.end() && marked[ins]) {
        return;
    }
    
    // 标记该指令
    marked[ins] = true;
    
    // 将该指令加入 work_list
    work_list.push_back(ins);
}

bool DeadCode::sweep(Function *func) {
    // TODO: 删除无用指令
    // 提示：
    // 1. 遍历函数的基本块，删除所有标记为true的指令
    // 2. 删除指令后，可能会导致其他指令的操作数变为无用，因此需要再次遍历函数的基本块
    // 3. 如果删除了指令，返回true，否则返回false
    // 4. 注意：删除指令时，需要先删除操作数的引用，然后再删除指令本身
    // 5. 删除指令时，需要注意指令的顺序，不能删除正在遍历的指令
    std::unordered_set<Instruction *> wait_del{};

    // 1. 收集所有未被标记的指令
    for (auto &bb : func->get_basic_blocks()) {
        for (auto &instr : bb.get_instructions()) {
            auto ins = &instr;
            // 如果指令未被标记，则加入待删除集合
            if (marked.find(ins) == marked.end() || !marked[ins]) {
                wait_del.insert(ins);
            }
        }
    }

    // 2. 执行删除
    for (auto ins : wait_del) {
        // 删除指令前，先删除操作数的引用
        ins->remove_all_operands();
        // 从基本块中删除指令
        auto bb = ins->get_parent();
        bb->erase_instr(ins);
        // if (bb) {
        //     bb->erase_instr(ins);
        //     ins_count++;
        // }
        ins_count++;
    }
    
    return not wait_del.empty(); // changed
}

bool DeadCode::is_critical(Instruction *ins) {
    // TODO: 判断指令是否是关键指令（不能被删除）
    // 提示：
    // 1. 如果是函数调用，且函数是纯函数，则无用
    // 2. 如果是无用的分支指令，则无用
    // 3. 如果是无用的返回指令，则无用
    // 4. 如果是无用的存储指令，则无用
    
    // 返回指令总是关键指令
    if (ins->is_ret()) {
        return true;
    }
    
    // 分支指令总是关键指令
    if (ins->is_br()) {
        return true;
    }
    
    // 存储指令：如果存储到全局变量或数组，则是关键指令
    if (ins->is_store()) {
        auto store_ins = static_cast<StoreInst *>(ins);
        auto lval = store_ins->get_lval();
        
        // 如果存储到全局变量，则是关键指令
        if (dynamic_cast<GlobalVariable *>(lval)) {
            return true;
        }
        
        // 如果存储到数组（通过 gep 访问），则是关键指令
        if (dynamic_cast<GetElementPtrInst *>(lval)) {
            return true;
        }
        
        // 其他存储指令不是关键指令
        return false;
    }
    
    // 函数调用：如果函数不是纯函数，则是关键指令
    if (ins->is_call()) {
        auto call_ins = static_cast<CallInst *>(ins);
        auto func = call_ins->func_;
        // 如果函数不在映射中（可能是声明），则认为是关键指令
        // 否则检查是否是纯函数
        try {
            if (!func_info->is_pure_function(func)) {
                return true;
            }
        } catch (...) {
            // 如果函数不在映射中，认为是关键指令
            return true;
        }
        // 纯函数调用不是关键指令
        return false;
    }
    
    // 其他指令不是关键指令
    return false;
}

void DeadCode::sweep_globally() {
    std::vector<Function *> unused_funcs;
    std::vector<GlobalVariable *> unused_globals;
    for (auto &f_r : m_->get_functions()) {
        if (f_r.get_use_list().size() == 0 and f_r.get_name() != "main")
            unused_funcs.push_back(&f_r);
    }
    for (auto &glob_var_r : m_->get_global_variable()) {
        if (glob_var_r.get_use_list().size() == 0)
            unused_globals.push_back(&glob_var_r);
    }
    // changed |= unused_funcs.size() or unused_globals.size();
    for (auto func : unused_funcs)
        m_->get_functions().erase(func);
    for (auto glob : unused_globals)
        m_->get_global_variable().erase(glob);
}
