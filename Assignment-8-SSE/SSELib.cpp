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
void SSE::reachability(const ICFGEdge* curEdge, const ICFGNode* snk) {
    /// TODO: your code starts from here
    const ICFGNode* curNode = curEdge->getDstNode();

    /// 第一次从 entry 进来：curEdge 的 src 为 nullptr，这里作为 DFS 的起点，
    /// 不把这条虚拟边加入 path，只从它的 dst（程序入口）往外扩展。
    if (curEdge->getSrcNode() == nullptr) {
        // 为这一次从 entry 到某个 sink 的搜索做初始化
        visited.clear();
        callstack.clear();
        path.clear();

        // 从入口节点的所有出边开始 DFS
        for (const ICFGEdge* outEdge : curNode->getOutEdges()) {
            reachability(outEdge, snk);
        }
        return;
    }

    // 将当前真实边加入当前路径
    path.push_back(curEdge);

    // 利用 <当前边, 当前调用栈> 做上下文敏感去重，避免在同一调用上下文中重复遍历环路
    ICFGEdgeStackPair state(curEdge, callstack);
    if (!visited.insert(state).second) {
        // 之前已经以同样的调用栈访问过这条边，直接回溯
        path.pop_back();
        return;
    }

    // 如果已经到达 sink（断言节点），收集并翻译这条路径
    if (curNode == snk) {
        collectAndTranslatePath();
        path.pop_back();
        return;
    }

    // 继续从当前节点向后遍历所有出边
    for (const ICFGEdge* outEdge : curNode->getOutEdges()) {
        // 对于调用边，在递归前入栈调用点，在返回后出栈，维持上下文敏感的调用栈
        if (const CallCFGEdge* callEdge = SVFUtil::dyn_cast<CallCFGEdge>(outEdge)) {
            callstack.push_back(callEdge->getSrcNode());
            reachability(outEdge, snk);
            callstack.pop_back();
        }
        // 对于返回边，在递归前弹出一层调用栈，递归结束后再恢复
        else if (SVFUtil::isa<RetCFGEdge>(outEdge)) {
            const ICFGNode* lastCall = nullptr;
            if (!callstack.empty()) {
                lastCall = callstack.back();
                callstack.pop_back();
                reachability(outEdge, snk);
                callstack.push_back(lastCall);
            }
            else {
                // 异常情况：没有调用栈仍然有返回边，直接当普通边处理
                reachability(outEdge, snk);
            }
        }
        else {
            // 普通 Intra 边
            reachability(outEdge, snk);
        }
    }

    // 回溯，弹出当前边
    path.pop_back();
}

/// TODO: collect each path once this method is called during reachability analysis, and
/// Collect each program path from the entry to each assertion of the program. In this function,
/// you will need (1) add each path into the paths set; (2) call translatePath to convert each path into Z3 expressions.
/// Note that translatePath returns true if the path is feasible, false if the path is infeasible; (3) If a path is feasible,
/// you will need to call assertchecking to verify the assertion (which is the last ICFGNode of this path); (4) reset z3 solver.
void SSE::collectAndTranslatePath() {
    /// TODO: your code starts from here
    if (path.empty())
        return;

    // (1) 把当前路径转换成字符串加入 paths（仅用于记录/测试）
    std::string pathStr;

    // 先记录第一个边的源节点（入口）
    const ICFGEdge* firstEdge = path.front();
    const ICFGNode* startNode = firstEdge->getSrcNode();
    if (startNode) {
        pathStr += std::to_string(startNode->getId());
    }

    // 依次追加每条边的目标节点
    for (const ICFGEdge* edge : path) {
        const ICFGNode* dst = edge->getDstNode();
        pathStr += "->";
        pathStr += std::to_string(dst->getId());
    }

    paths.insert(pathStr);

    // (2) 调用 translatePath，将该路径上的语句翻译为 Z3 约束
    bool feasible = translatePath(path);

    // (3) 若路径可行，则最后一个节点应为断言调用点，对其进行断言检查
    if (feasible) {
        const ICFGNode* lastNode = path.back()->getDstNode();
        assertchecking(lastNode);
    }

    // (4) 重置 z3 solver，为下一条路径分析做准备
    resetSolver();
}

/// TODO: Implement handling of function calls
void SSE::handleCall(const CallCFGEdge* calledge) {
    /// TODO: your code starts from here
    expr_vector actualArgs(getCtx());
    auto& callPEs = calledge->getCallPEs();
    for (auto callPE : callPEs) {
        expr rhs = getZ3Expr(callPE->getRHSVarID());
        actualArgs.push_back(rhs);
    }

    // 进入被调函数：把调用点 ICFGNode 压入 callingCtx
    pushCallingCtx(calledge->getSrcNode());

    // 把实际参数约束到形式参数（callee 侧 LHS）
    u32_t idx = 0;
    for (auto callPE : callPEs) {
        expr lhs = getZ3Expr(callPE->getLHSVarID());
        addToSolver(lhs == actualArgs[idx++]);
    }
}

/// TODO: Implement handling of function returns
void SSE::handleRet(const RetCFGEdge* retEdge) {
    /// TODO: your code starts from here
    auto retPE = retEdge->getRetPE();

    // formal return value（callee 里的返回值）
    expr rhs = getCtx().int_val(0);
    if (retPE) {
        rhs = getZ3Expr(retPE->getRHSVarID());
    }

    // 离开被调函数：弹出调用上下文
    popCallingCtx();

    // 如果有返回值，把它约束到 caller 的接收变量上
    if (retPE) {
        expr lhs = getZ3Expr(retPE->getLHSVarID());
        addToSolver(lhs == rhs);
    }
}

/// TODO: Implement handling of branch statements inside a function
/// Return true if the path is feasible, false otherwise.
/// A given if/else branch on the ICFG looks like the following:
///       	     ICFGNode1 (condition %cmp)
///       	     1	/    \  0
///       	  ICFGNode2   ICFGNode3
/// edge->getCondition() returns the branch condition variable (%cmp) of type SVFValue* (for if/else) or a numeric condition variable (for switch).
/// Given the condition variable, you could obtain the SVFVar ID via "edge->getCondition()->getId()"
/// edge->getCondition() returns nullptr if this IntraCFGEdge is not a branch.
/// edge->getSuccessorCondValue() returns the actual condition value (1/0 for if/else) when this branch/IntraCFGEdge is executed. For example, the successorCondValue is 1 on the edge from ICFGNode1 to ICFGNode2, and 0 on the edge from ICFGNode1 to ICFGNode3
bool SSE::handleBranch(const IntraCFGEdge* edge) {
    /// TODO: your code starts from here
    const SVFValue* condVal = edge->getCondition();
    assert(condVal && "IntraCFGEdge with branch must have a condition!");

    expr cond = getZ3Expr(condVal->getId());
    // 当前这条分支真正被执行时，条件求值应等于 successorCondValue (0/1)
    expr succ = getCtx().int_val((s32_t)edge->getSuccessorCondValue());

    // 先用 push/pop 做一次“试探”，看加上 cond == succ 约束后是否仍可满足
    getSolver().push();
    addToSolver(cond == succ);
    z3::check_result res = getSolver().check();
    getSolver().pop();

    if (res == z3::unsat) {
        // 该分支在当前路径下不可行
        return false;
    }
    else {
        // 该分支可行，把约束真正加入 solver
        addToSolver(cond == succ);
        return true;
    }
}

/// TODO: Translate AddrStmt, CopyStmt, LoadStmt, StoreStmt, GepStmt and CmpStmt
/// Translate AddrStmt, CopyStmt, LoadStmt, StoreStmt, GepStmt, BinaryOPStmt, CmpStmt, SelectStmt, and PhiStmt
bool SSE::handleNonBranch(const IntraCFGEdge* edge) {
    const ICFGNode* dstNode = edge->getDstNode();
    const ICFGNode* srcNode = edge->getSrcNode();
    DBOP(if(!SVFUtil::isa<CallICFGNode>(dstNode) && !SVFUtil::isa<RetICFGNode>(dstNode)) std::cout << "\n## Analyzing "<< dstNode->toString() << "\n");

    for (const SVFStmt *stmt : dstNode->getSVFStmts())
    {
        if (const AddrStmt *addr = SVFUtil::dyn_cast<AddrStmt>(stmt))
        {
            // TODO: implement AddrStmt handler here
            expr obj = getMemObjAddress(addr->getRHSVarID());
            // lhs: 左边指针变量
            expr lhs = getZ3Expr(addr->getLHSVarID());
            addToSolver(lhs == obj);
        }
        else if (const CopyStmt *copy = SVFUtil::dyn_cast<CopyStmt>(stmt))
        {
            // TODO: implement CopyStmt handler her
            expr lhs = getZ3Expr(copy->getLHSVarID());
            expr rhs = getZ3Expr(copy->getRHSVarID());
            addToSolver(lhs == rhs);
        }
        else if (const LoadStmt *load = SVFUtil::dyn_cast<LoadStmt>(stmt))
        {
            // TODO: implement LoadStmt handler here
            expr lhs = getZ3Expr(load->getLHSVarID());
            expr rhs = getZ3Expr(load->getRHSVarID());   // 地址
            addToSolver(lhs == z3Mgr->loadValue(rhs));
        }
        else if (const StoreStmt *store = SVFUtil::dyn_cast<StoreStmt>(stmt))
        {
            // TODO: implement StoreStmt handler here
            expr lhs = getZ3Expr(store->getLHSVarID());  // 地址
            expr rhs = getZ3Expr(store->getRHSVarID());  // 要存的值
            z3Mgr->storeValue(lhs, rhs);
        }
        else if (const GepStmt *gep = SVFUtil::dyn_cast<GepStmt>(stmt))
        {
            // TODO: implement GepStmt handler here
            expr lhs = getZ3Expr(gep->getLHSVarID());
            expr rhs = getZ3Expr(gep->getRHSVarID());   // base pointer
            // 计算偏移（依据当前调用上下文）
            s32_t offset = z3Mgr->getGepOffset(gep, callingCtx);
            // 得到偏移字段的新地址
            expr gepAddress = z3Mgr->getGepObjAddress(rhs, offset);
            addToSolver(lhs == gepAddress);
        }
            /// Given a CmpStmt "r = a > b"
            /// cmp->getOpVarID(0)/cmp->getOpVarID(1) returns the first/second operand, i.e., "a" and "b"
            /// cmp->getResID() returns the result operand "r" and cmp->getPredicate() gives you the predicate ">"
            /// Find the comparison predicates in "class CmpStmt:Predicate" under SVF/svf/include/SVFIR/SVFStatements.h
            /// You are only required to handle integer predicates, including ICMP_EQ, ICMP_NE, ICMP_UGT, ICMP_UGE, ICMP_ULT, ICMP_ULE, ICMP_SGT, ICMP_SGE, ICMP_SLE, ICMP_SLT
            /// We assume integer-overflow-free in this assignment
        else if (const CmpStmt *cmp = SVFUtil::dyn_cast<CmpStmt>(stmt))
        {
            // TODO: implement CmpStmt handler here
            expr op0 = getZ3Expr(cmp->getOpVarID(0));
            expr op1 = getZ3Expr(cmp->getOpVarID(1));
            expr res = getZ3Expr(cmp->getResID());
            expr one  = getCtx().int_val(1);
            expr zero = getCtx().int_val(0);
            switch (cmp->getPredicate())
            {
                case CmpStmt::ICMP_EQ:
                    addToSolver(res == ite(op0 == op1, one, zero));
                    break;
                case CmpStmt::ICMP_NE:
                    addToSolver(res == ite(op0 != op1, one, zero));
                    break;
                case CmpStmt::ICMP_UGT:
                case CmpStmt::ICMP_SGT:
                    addToSolver(res == ite(op0 > op1, one, zero));
                    break;
                case CmpStmt::ICMP_UGE:
                case CmpStmt::ICMP_SGE:
                    addToSolver(res == ite(op0 >= op1, one, zero));
                    break;
                case CmpStmt::ICMP_ULT:
                case CmpStmt::ICMP_SLT:
                    addToSolver(res == ite(op0 < op1, one, zero));
                    break;
                case CmpStmt::ICMP_ULE:
                case CmpStmt::ICMP_SLE:
                    addToSolver(res == ite(op0 <= op1, one, zero));
                    break;
                default:
                    assert(false && "unhandled integer comparison predicate");
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