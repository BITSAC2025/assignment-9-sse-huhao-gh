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

    const ICFGNode *curNode = curEdge->getDstNode();

    // 起始：从 GlobalICFGNode 出发的“虚拟边”（src 为 nullptr）
    if (curEdge->getSrcNode() == nullptr) {
        // 对每个 sink（assert 调用点）单独做 DFS，因此先清空搜索状态
        visited.clear();
        callstack.clear();
        path.clear();

        // 从 GlobalICFGNode 的所有出边开始 DFS
        for (const ICFGEdge *outEdge : curNode->getOutEdges()) {
            reachability(outEdge, snk);
        }
        return;
    }

    // === 下面是真实的 ICFGEdge 的处理 ===

    // 把当前边加入当前路径
    path.push_back(curEdge);

    // 用 <当前边, 当前调用栈> 作为 key 做上下文敏感去重
    ICFGEdgeStackPair state(curEdge, callstack);
    if (!visited.insert(state).second) {
        // 在同一调用上下文下，这条边已经访问过了（避免在同一个上下文中反复绕圈）
        path.pop_back();
        return;
    }

    // 如果当前节点已经是 sink（某个 svf_assert 调用点），收集并翻译这条路径
    if (curNode == snk) {
        collectAndTranslatePath();
        path.pop_back();
        return;
    }

    // 否则继续从当前节点往后 DFS
    for (const ICFGEdge *outEdge : curNode->getOutEdges()) {
        if (const CallCFGEdge *callEdge = SVFUtil::dyn_cast<CallCFGEdge>(outEdge)) {
            // 函数调用：先把调用点压栈，再递归遍历 call edge
            callstack.push_back(callEdge->getSrcNode());
            reachability(outEdge, snk);
            callstack.pop_back();
        } else if (const RetCFGEdge *retEdge = SVFUtil::dyn_cast<RetCFGEdge>(outEdge)) {
            // 函数返回：弹出一层调用点，再递归遍历 ret edge，回来后恢复
            if (!callstack.empty()) {
                const ICFGNode *lastCall = callstack.back();
                callstack.pop_back();
                reachability(outEdge, snk);
                callstack.push_back(lastCall);
            } else {
                // 理论上不该出现（没有调用栈却有返回边），当普通边处理
                reachability(outEdge, snk);
            }
        } else {
            // 普通 IntraCFGEdge
            reachability(outEdge, snk);
        }
    }

    // 回溯当前边
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

    // (1) 把当前路径转成字符串，加入 paths 集合（用于测试/调试）
    std::string pathStr;

    const ICFGEdge *firstEdge = path.front();
    const ICFGNode *startNode = firstEdge->getSrcNode();
    if (startNode) {
        pathStr += std::to_string(startNode->getId());
    }

    for (const ICFGEdge *edge : path) {
        const ICFGNode *dst = edge->getDstNode();
        pathStr += "->";
        pathStr += std::to_string(dst->getId());
    }
    paths.insert(pathStr);

    // (2) 在翻译整条路径前，先把 GlobalICFGNode 上的初始化语句翻译一遍
    bool feasible = true;
    if (startNode && SVFUtil::isa<GlobalICFGNode>(startNode)) {
        // 伪造一条 IntraCFGEdge：src = nullptr, dst = GlobalICFGNode
        const IntraCFGEdge fakeGlobalEdge(nullptr, const_cast<ICFGNode *>(startNode));
        feasible = handleNonBranch(&fakeGlobalEdge);
    }

    // 再翻译实际路径中的各个语句
    if (feasible)
        feasible = translatePath(path);

    // (3) 可行路径：最后一个结点是断言调用点，做断言检查
    if (feasible) {
        const ICFGNode *lastNode = path.back()->getDstNode();
        assertchecking(lastNode);
    }

    // (4) 为下一条路径重置 solver 和调用上下文
    resetSolver();
}

/// TODO: Implement handling of function calls
void SSE::handleCall(const CallCFGEdge* callEdge) {
    /// TODO: your code starts from here

    // 进入被调函数：记录调用点作为 Z3 变量命名的调用上下文
    pushCallingCtx(callEdge->getSrcNode());

    // 用 CallPE 把 caller 的实参和 callee 的形参连起来
    const auto &callPEs = callEdge->getCallPEs();
    for (auto pe : callPEs) {
        expr lhs = getZ3Expr(pe->getLHSVarID());  // callee 里的形式参数
        expr rhs = getZ3Expr(pe->getRHSVarID());  // caller 里的实际参数
        addToSolver(lhs == rhs);
    }
}

/// TODO: Implement handling of function returns
void SSE::handleRet(const RetCFGEdge* retEdge) {
    /// TODO: your code starts from here

    const RetPE *retPE = retEdge->getRetPE();

    // 先在被调函数上下文下拿到返回值（如果有）
    expr retVal(getCtx());
    bool hasRetVal = false;
    if (retPE) {
        retVal = getZ3Expr(retPE->getRHSVarID()); // callee 的返回值
        hasRetVal = true;
    }

    // 弹出调用上下文，切回 caller
    popCallingCtx();

    // 在 caller 上下文中把返回值约束给接收返回值的变量
    if (retPE && hasRetVal) {
        expr lhs = getZ3Expr(retPE->getLHSVarID()); // caller 里的接收变量
        addToSolver(lhs == retVal);
    }
}

/// TODO: Implement handling of branch statements inside a function
/// Return true if the path is feasible, false otherwise.
bool SSE::handleBranch(const IntraCFGEdge* edge) {
    /// TODO: your code starts from here

    const SVFValue *condVal = edge->getCondition();
    assert(condVal && "Branch IntraCFGEdge must have a condition!");

    // cmp 的结果（一般是 0/1），以及该边对应的条件值（1/0, 或 switch 的某个 case 值）
    expr cond = getZ3Expr(condVal->getId());
    expr succ = getCtx().int_val((s32_t)edge->getSuccessorCondValue());

    // 先在一个 push 的 scope 里试探性加上 cond==succ，看当前路径下是否可行
    getSolver().push();
    addToSolver(cond == succ);
    z3::check_result res = getSolver().check();
    getSolver().pop();

    if (res == z3::unsat) {
        // 该分支在当前路径约束下不可达
        return false;
    } else {
        // 分支可行，把约束真正加进 solver
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
            // lhs = &obj
            expr lhs = getZ3Expr(addr->getLHSVarID());
            expr objAddr = getMemObjAddress(addr->getRHSVarID());
            addToSolver(lhs == objAddr);
        }
        else if (const CopyStmt *copy = SVFUtil::dyn_cast<CopyStmt>(stmt))
        {
            // 简单赋值：lhs = rhs
            expr lhs = getZ3Expr(copy->getLHSVarID());
            expr rhs = getZ3Expr(copy->getRHSVarID());
            addToSolver(lhs == rhs);
        }
        else if (const LoadStmt *load = SVFUtil::dyn_cast<LoadStmt>(stmt))
        {
            // lhs = *ptr
            expr lhs = getZ3Expr(load->getLHSVarID());
            expr ptr = getZ3Expr(load->getRHSVarID());
            expr val = z3Mgr->loadValue(ptr);
            addToSolver(lhs == val);
        }
        else if (const StoreStmt *store = SVFUtil::dyn_cast<StoreStmt>(stmt))
        {
            // *ptr = val
            expr ptr = getZ3Expr(store->getLHSVarID());
            expr val = getZ3Expr(store->getRHSVarID());
            z3Mgr->storeValue(ptr, val);
        }
        else if (const GepStmt *gep = SVFUtil::dyn_cast<GepStmt>(stmt))
        {
            // lhs = base + offset
            expr lhs  = getZ3Expr(gep->getLHSVarID());
            expr base = getZ3Expr(gep->getRHSVarID());
            s32_t offset = z3Mgr->getGepOffset(gep, callingCtx);
            expr gepAddr = z3Mgr->getGepObjAddress(base, (u32_t)offset);
            addToSolver(lhs == gepAddr);
        }
        else if (const CmpStmt *cmp = SVFUtil::dyn_cast<CmpStmt>(stmt))
        {
            // r = (a ? b)，结果 r 用 0/1 表示
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

                // 无符号比较：用 bitvector 的 ugt/uge/ult/ule
                case CmpStmt::ICMP_UGT:
                    addToSolver(res == ite(ugt(int2bv(32, op0), int2bv(32, op1)), one, zero));
                    break;
                case CmpStmt::ICMP_UGE:
                    addToSolver(res == ite(uge(int2bv(32, op0), int2bv(32, op1)), one, zero));
                    break;
                case CmpStmt::ICMP_ULT:
                    addToSolver(res == ite(ult(int2bv(32, op0), int2bv(32, op1)), one, zero));
                    break;
                case CmpStmt::ICMP_ULE:
                    addToSolver(res == ite(ule(int2bv(32, op0), int2bv(32, op1)), one, zero));
                    break;

                // 有符号比较：用整数的 > >= < <=
                case CmpStmt::ICMP_SGT:
                    addToSolver(res == ite(op0 > op1, one, zero));
                    break;
                case CmpStmt::ICMP_SGE:
                    addToSolver(res == ite(op0 >= op1, one, zero));
                    break;
                case CmpStmt::ICMP_SLT:
                    addToSolver(res == ite(op0 < op1, one, zero));
                    break;
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
