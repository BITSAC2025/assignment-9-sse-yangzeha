/**
 * SSELib.cpp
 * @author kisslune 
 */

#include "SSEHeader.h"
#include "Util/Options.h"

using namespace SVF;
using namespace SVFUtil;
using namespace llvm;
using namespace z3;

/// TODO: Implement your context-sensitive ICFG traversal here to traverse each program path (once for any loop) from
/// You will need to collect each path from src node to snk node and then add the path to the `paths` set by
/// calling the `collectAndTranslatePath` method, in which translatePath method is called.
/// This implementation, slightly different from Assignment-1, requires ICFGNode* as the first argument.
// void SSE::reachability(const ICFGEdge* curEdge, const ICFGNode* snk) {
//     const ICFGNode* curNode = curEdge->getDstNode();
    
//     // 空指针检查
//     if (!curNode) {
//         return;
//     }
    
//     // 到达目标节点
//     if (curNode == snk) {
//         collectAndTranslatePath();  // ✅ 无参数版本
//         return;
//     }
    
//     // 构造上下文敏感的visited状态
//     ICFGEdgeStackPair curPair(curEdge, callstack);
    
//     // 避免重复访问
//     if (visited.count(curPair)) {
//         return;
//     }
    
//     // 标记为已访问
//     visited.insert(curPair);
    
//     // 将边加入路径（排除起始边）
//     if (curEdge->getSrcNode() != nullptr) {
//         path.push_back(curEdge);
//     }
    
//     // 遍历所有出边
//     for (const ICFGEdge* outEdge : curNode->getOutEdges()) {
//         if (const CallCFGEdge* callEdge = SVFUtil::dyn_cast<CallCFGEdge>(outEdge)) {
//             // 函数调用：压入调用栈
//             callstack.push_back(curNode);
//             reachability(outEdge, snk);
//             callstack.pop_back();
//         }
//         else if (const RetCFGEdge* retEdge = SVFUtil::dyn_cast<RetCFGEdge>(outEdge)) {
//             // 函数返回：检查调用栈匹配（上下文敏感）
//             if (!callstack.empty()) {
//                 reachability(outEdge, snk);
//             }
//         }
//         else {
//             // 普通过程内边
//             reachability(outEdge, snk);
//         }
//     }
    
//     // 回溯
//     if (curEdge->getSrcNode() != nullptr) {
//         path.pop_back();
//     }
//     visited.erase(curPair);
// }
// void SSE::reachability(const ICFGEdge* curEdge, const ICFGNode* snk) {
//     const ICFGNode* curNode = curEdge->getDstNode();
    
//     // 空指针检查
//     if (!curNode) {
//         return;
//     }
    
//     // ⭐ 关键修改：先加边到path（在检查是否到达sink之前）
//     bool isStartEdge = (curEdge->getSrcNode() == nullptr);
//     if (!isStartEdge) {
//         path.push_back(curEdge);
//     }
    
//     // 到达目标节点
//     if (curNode == snk) {
//         collectAndTranslatePath();
//         // 回溯
//         if (!isStartEdge) {
//             path.pop_back();
//         }
//         return;
//     }
    
//     // 构造上下文敏感的visited状态
//     ICFGEdgeStackPair curPair(curEdge, callstack);
    
//     // 避免重复访问
//     if (visited.count(curPair)) {
//         if (!isStartEdge) {
//             path.pop_back();
//         }
//         return;
//     }
    
//     // 标记为已访问
//     visited.insert(curPair);
    
//     // 遍历所有出边
//     for (const ICFGEdge* outEdge : curNode->getOutEdges()) {
//         if (const CallCFGEdge* callEdge = SVFUtil::dyn_cast<CallCFGEdge>(outEdge)) {
//             // 函数调用：压入调用栈
//             callstack.push_back(curNode);
//             reachability(outEdge, snk);
//             callstack.pop_back();
//         }
//         else if (const RetCFGEdge* retEdge = SVFUtil::dyn_cast<RetCFGEdge>(outEdge)) {
//             // 函数返回：检查调用栈匹配（上下文敏感）
//             if (!callstack.empty()) {
//                 reachability(outEdge, snk);
//             }
//         }
//         else {
//             // 普通过程内边
//             reachability(outEdge, snk);
//         }
//     }
    
//     // 回溯
//     if (!isStartEdge) {
//         path.pop_back();
//     }
//     visited.erase(curPair);
// }
void SSE::reachability(const ICFGEdge* curEdge, const ICFGNode* snk) {
    const ICFGNode* curNode = curEdge->getDstNode();
    
    if (!curNode) {
        return;
    }
    
    bool isStartEdge = (curEdge->getSrcNode() == nullptr);
    if (!isStartEdge) {
        path.push_back(curEdge);
    }
    
    if (curNode == snk) {
        collectAndTranslatePath();
        if (!isStartEdge) {
            path.pop_back();
        }
        return;
    }
    
    ICFGEdgeStackPair curPair(curEdge, callstack);
    
    if (visited.count(curPair)) {
        if (!isStartEdge) {
            path.pop_back();
        }
        return;
    }
    
    visited.insert(curPair);
    
    for (const ICFGEdge* outEdge : curNode->getOutEdges()) {
        if (const CallCFGEdge* callEdge = SVFUtil::dyn_cast<CallCFGEdge>(outEdge)) {
            callstack.push_back(curNode);
            reachability(outEdge, snk);
            callstack.pop_back();
        }
        else if (const RetCFGEdge* retEdge = SVFUtil::dyn_cast<RetCFGEdge>(outEdge)) {
            // ⭐ 修改：检查调用栈匹配（上下文敏感的关键！）
            if (!callstack.empty() && callstack.back() == retEdge->getCallSite()) {
                reachability(outEdge, snk);
            }
        }
        else {
            reachability(outEdge, snk);
        }
    }
    
    if (!isStartEdge) {
        path.pop_back();
    }
    visited.erase(curPair);
}
/// TODO: collect each path once this method is called during reachability analysis, and
/// Collect each program path from the entry to each assertion of the program. In this function,
/// you will need (1) add each path into the paths set; (2) call translatePath to convert each path into Z3 expressions.
/// Note that translatePath returns true if the path is feasible, false if the path is infeasible; (3) If a path is feasible,
/// you will need to call assertchecking to verify the assertion (which is the last ICFGNode of this path); (4) reset z3 solver.
// void SSE::collectAndTranslatePath() {
//     // 检查路径是否为空
//     if (path.empty()) {
//         return;
//     }
    
//     // 1. 构建路径字符串用于存储到paths集合
//     std::string pathStr = "";
//     for (const ICFGEdge* edge : path) {
//         if (edge && edge->getDstNode()) {
//             pathStr += std::to_string(edge->getDstNode()->getId()) + "->";
//         }
//     }
    
//     // 将路径字符串添加到paths集合
//     paths.insert(pathStr);
    
//     // 2. 将路径转换为Z3约束表达式
//     bool feasible = translatePath(path);
    
//     // 3. 如果路径可行，验证断言
//     if (feasible) {
//         // 获取路径最后一个节点（sink节点）
//         const ICFGNode* sink = path.back()->getDstNode();
//         if (sink) {
//             assertchecking(sink);
//         }
//     }
    
//     // 4. 重置Z3求解器（注意：这里不调用resetSolver，因为analyse()中会统一调用）
// }
void SSE::collectAndTranslatePath() {
    // 检查路径是否为空
    if (path.empty()) {
        return;
    }
    
    // 1. 构建路径字符串用于存储到paths集合
    std::string pathStr = "";
    for (const ICFGEdge* edge : path) {
        if (edge && edge->getDstNode()) {
            pathStr += std::to_string(edge->getDstNode()->getId()) + "->";
        }
    }
    
    // 将路径字符串添加到paths集合
    paths.insert(pathStr);
    
    // 2. 将路径转换为Z3约束表达式
    bool feasible = translatePath(path);
    
    // 3. 如果路径可行，验证断言
    if (feasible) {
        // 获取路径最后一个节点（sink节点）
        const ICFGNode* sink = path.back()->getDstNode();
        if (sink) {
            assertchecking(sink);
        }
    }
    
    // 4. ⭐关键：每条路径验证后必须重置求解器
    resetSolver();
}
/// TODO: Implement handling of function calls
void SSE::handleCall(const CallCFGEdge* callEdge) {
    // 获取调用点
    const ICFGNode* callNode = callEdge->getCallSite();
    
    // 压入调用上下文（用于符号执行）
    pushCallingCtx(const_cast<ICFGNode*>(callNode));
    
    // 处理实参到形参的赋值
    for (const SVFStmt* stmt : callEdge->getCallPEs()) {
        if (const CopyStmt* copy = SVFUtil::dyn_cast<CopyStmt>(stmt)) {
            expr lhs = getZ3Expr(copy->getLHSVarID());
            expr rhs = getZ3Expr(copy->getRHSVarID());
            addToSolver(lhs == rhs);
        }
    }
}

/// TODO: Implement handling of function returns
void SSE::handleRet(const RetCFGEdge* retEdge) {
    // 处理返回值赋值
    const SVFStmt* retPE = retEdge->getRetPE();
    if (retPE != nullptr) {
        if (const CopyStmt* copy = SVFUtil::dyn_cast<CopyStmt>(retPE)) {
            expr lhs = getZ3Expr(copy->getLHSVarID());
            expr rhs = getZ3Expr(copy->getRHSVarID());
            addToSolver(lhs == rhs);
        }
    }
    
    // 弹出调用上下文
    popCallingCtx();
}

/// TODO: Implement handling of branch statements inside a function
/// Return true if the path is feasible, false otherwise.
// bool SSE::handleBranch(const IntraCFGEdge* edge) {
//     // 获取分支条件变量
//     const SVFValue* condition = edge->getCondition();
//     if (condition == nullptr) {
//         return true; // 不是条件分支
//     }
    
//     // 获取条件的Z3表达式
//     expr condExpr = getZ3Expr(condition->getId());
    
//     // 获取分支方向 (1=true分支, 0=false分支)
//     s64_t branchValue = edge->getSuccessorCondValue();
    
//     // 添加路径约束
//     addToSolver(condExpr == getCtx().int_val(branchValue));
    
//     // 检查路径可行性
//     if (getSolver().check() == z3::unsat) {
//         return false; // 路径不可行
//     }
    
//     return true;
// }
bool SSE::handleBranch(const IntraCFGEdge* edge) {
    // 获取分支条件变量
    const SVFValue* condition = edge->getCondition();
    if (condition == nullptr) {
        return true; // 不是条件分支
    }
    
    // 获取条件的Z3表达式
    expr condExpr = getZ3Expr(condition->getId());
    
    // 获取分支方向 (1=true分支, 0=false分支)
    s64_t branchValue = edge->getSuccessorCondValue();
    
    // ⭐ 关键修改：显式转换为int类型
    addToSolver(condExpr == getCtx().int_val(static_cast<int>(branchValue)));
    
    // 检查路径可行性
    if (getSolver().check() == z3::unsat) {
        return false; // 路径不可行
    }
    
    return true;
}
/// TODO: Translate AddrStmt, CopyStmt, LoadStmt, StoreStmt, GepStmt and CmpStmt
bool SSE::handleNonBranch(const IntraCFGEdge* edge) {
    const ICFGNode* dstNode = edge->getDstNode();
    const ICFGNode* srcNode = edge->getSrcNode();
    DBOP(if(!SVFUtil::isa<CallICFGNode>(dstNode) && !SVFUtil::isa<RetICFGNode>(dstNode)) std::cout << "\n## Analyzing "<< dstNode->toString() << "\n");

    for (const SVFStmt *stmt : dstNode->getSVFStmts())
    {
        if (const AddrStmt *addr = SVFUtil::dyn_cast<AddrStmt>(stmt))
        {
            // AddrStmt: x = &obj
            expr lhs = getZ3Expr(addr->getLHSVarID());
            expr rhs = getMemObjAddress(addr->getRHSVarID());
            addToSolver(lhs == rhs);
        }
        else if (const CopyStmt *copy = SVFUtil::dyn_cast<CopyStmt>(stmt))
        {
            // CopyStmt: x = y
            expr lhs = getZ3Expr(copy->getLHSVarID());
            expr rhs = getZ3Expr(copy->getRHSVarID());
            addToSolver(lhs == rhs);
        }
        else if (const LoadStmt *load = SVFUtil::dyn_cast<LoadStmt>(stmt))
        {
            // LoadStmt: x = *ptr
            expr lhs = getZ3Expr(load->getLHSVarID());
            expr ptr = getZ3Expr(load->getRHSVarID());
            expr value = z3Mgr->loadValue(ptr);
            addToSolver(lhs == value);
        }
        else if (const StoreStmt *store = SVFUtil::dyn_cast<StoreStmt>(stmt))
        {
            // StoreStmt: *ptr = x
            expr ptr = getZ3Expr(store->getLHSVarID());
            expr value = getZ3Expr(store->getRHSVarID());
            z3Mgr->storeValue(ptr, value);
        }
        else if (const GepStmt *gep = SVFUtil::dyn_cast<GepStmt>(stmt))
        {
            // GepStmt: ptr2 = ptr1 + offset
            expr lhs = getZ3Expr(gep->getLHSVarID());
            expr ptr = getZ3Expr(gep->getRHSVarID());
            u32_t offset = z3Mgr->getGepOffset(gep, callingCtx);
            expr fieldAddr = z3Mgr->getGepObjAddress(ptr, offset);
            addToSolver(lhs == fieldAddr);
        }
        else if (const CmpStmt *cmp = SVFUtil::dyn_cast<CmpStmt>(stmt))
        {
            // CmpStmt: res = op0 cmp op1
            expr op0 = getZ3Expr(cmp->getOpVarID(0));
            expr op1 = getZ3Expr(cmp->getOpVarID(1));
            expr res = getZ3Expr(cmp->getResID());
            
            switch (cmp->getPredicate()) {
                case CmpStmt::ICMP_EQ:  // ==
                    addToSolver(res == ite(op0 == op1, getCtx().int_val(1), getCtx().int_val(0)));
                    break;
                case CmpStmt::ICMP_NE:  // !=
                    addToSolver(res == ite(op0 != op1, getCtx().int_val(1), getCtx().int_val(0)));
                    break;
                case CmpStmt::ICMP_UGT: // > (unsigned)
                case CmpStmt::ICMP_SGT: // > (signed)
                    addToSolver(res == ite(op0 > op1, getCtx().int_val(1), getCtx().int_val(0)));
                    break;
                case CmpStmt::ICMP_UGE: // >= (unsigned)
                case CmpStmt::ICMP_SGE: // >= (signed)
                    addToSolver(res == ite(op0 >= op1, getCtx().int_val(1), getCtx().int_val(0)));
                    break;
                case CmpStmt::ICMP_ULT: // < (unsigned)
                case CmpStmt::ICMP_SLT: // < (signed)
                    addToSolver(res == ite(op0 < op1, getCtx().int_val(1), getCtx().int_val(0)));
                    break;
                case CmpStmt::ICMP_ULE: // <= (unsigned)
                case CmpStmt::ICMP_SLE: // <= (signed)
                    addToSolver(res == ite(op0 <= op1, getCtx().int_val(1), getCtx().int_val(0)));
                    break;
                default:
                    assert(false && "Unsupported comparison predicate");
            }
        }
        else if (const BinaryOPStmt *binary = SVFUtil::dyn_cast<BinaryOPStmt>(stmt))
        {
            expr op0 = getZ3Expr(binary->getOpVarID(0));
            expr op1 = getZ3Expr(binary->getOpVarID(1));
            expr res = getZ3Expr(binary->getResID());
            switch (binary->getOpcode())
            {
                case BinaryOperator::Add:
                    addToSolver(res == op0 + op1);
                    break;
                case BinaryOperator::Sub:
                    addToSolver(res == op0 - op1);
                    break;
                case BinaryOperator::Mul:
                    addToSolver(res == op0 * op1);
                    break;
                case BinaryOperator::SDiv:
                    addToSolver(res == op0 / op1);
                    break;
                case BinaryOperator::SRem:
                    addToSolver(res == op0 % op1);
                    break;
                case BinaryOperator::Xor:
                    addToSolver(res == bv2int(int2bv(32, op0) ^ int2bv(32, op1), 1));
                    break;
                case BinaryOperator::And:
                    addToSolver(res == bv2int(int2bv(32, op0) & int2bv(32, op1), 1));
                    break;
                case BinaryOperator::Or:
                    addToSolver(res == bv2int(int2bv(32, op0) | int2bv(32, op1), 1));
                    break;
                case BinaryOperator::AShr:
                    addToSolver(res == bv2int(ashr(int2bv(32, op0), int2bv(32, op1)), 1));
                    break;
                case BinaryOperator::Shl:
                    addToSolver(res == bv2int(shl(int2bv(32, op0), int2bv(32, op1)), 1));
                    break;
                default:
                    assert(false && "implement this part");
            }
        }
        else if (const BranchStmt *br = SVFUtil::dyn_cast<BranchStmt>(stmt))
        {
            DBOP(std::cout << "\t skip handled when traversal Conditional IntraCFGEdge \n");
        }
        else if (const SelectStmt *select = SVFUtil::dyn_cast<SelectStmt>(stmt)) {
            expr res = getZ3Expr(select->getResID());
            expr tval = getZ3Expr(select->getTrueValue()->getId());
            expr fval = getZ3Expr(select->getFalseValue()->getId());
            expr cond = getZ3Expr(select->getCondition()->getId());
            addToSolver(res == ite(cond == getCtx().int_val(1), tval, fval));
        }
        else if (const PhiStmt *phi = SVFUtil::dyn_cast<PhiStmt>(stmt)) {
            expr res = getZ3Expr(phi->getResID());
            bool opINodeFound = false;
            for(u32_t i = 0; i < phi->getOpVarNum(); i++){
                assert(srcNode && "we don't have a predecessor ICFGNode?");
                if (srcNode->getFun()->postDominate(srcNode->getBB(),phi->getOpICFGNode(i)->getBB()))
                {
                    expr ope = getZ3Expr(phi->getOpVar(i)->getId());
                    addToSolver(res == ope);
                    opINodeFound = true;
                }
            }
            assert(opINodeFound && "predecessor ICFGNode of this PhiStmt not found?");
        }
    }

    return true;
}

/// Traverse each program path
bool SSE::translatePath(std::vector<const ICFGEdge*>& path) {
    for (const ICFGEdge* edge : path) {
        if (const IntraCFGEdge* intraEdge = SVFUtil::dyn_cast<IntraCFGEdge>(edge)) {
            if (handleIntra(intraEdge) == false)
                return false;
        }
        else if (const CallCFGEdge* call = SVFUtil::dyn_cast<CallCFGEdge>(edge)) {
            handleCall(call);
        }
        else if (const RetCFGEdge* ret = SVFUtil::dyn_cast<RetCFGEdge>(edge)) {
            handleRet(ret);
        }
        else
            assert(false && "what other edges we have?");
    }

    return true;
}

/// Program entry
void SSE::analyse() {
    for (const ICFGNode* src : identifySources()) {
        assert(SVFUtil::isa<GlobalICFGNode>(src) && "reachability should start with GlobalICFGNode!");
        for (const ICFGNode* sink : identifySinks()) {
            const IntraCFGEdge startEdge(nullptr, const_cast<ICFGNode*>(src));
            /// start traversing from the entry to each assertion and translate each path
            reachability(&startEdge, sink);
            resetSolver();
        }
    }
}
