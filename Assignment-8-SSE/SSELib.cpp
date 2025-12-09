/**
 * SSELib.cpp
 * @author kisslune
 */

#include "SSEHeader.h"
#include "Util/Options.h"
#include <sstream>

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

    if (curNode == snk) {
        path.push_back(curEdge);
        collectAndTranslatePath();
        path.pop_back();
        return;
    }

    ICFGEdgeStackPair curPair(curEdge, callstack);

    auto insertRes = visited.emplace(curPair);
    if (!insertRes.second) {
        return;
    }

    path.push_back(curEdge);

    for (const ICFGEdge* outEdge : curNode->getOutEdges()) {
        if (const CallCFGEdge* callEdge = SVFUtil::dyn_cast<CallCFGEdge>(outEdge)) {
            callstack.push_back(curNode);
            reachability(callEdge, snk);
            callstack.pop_back();
        } else if (const RetCFGEdge* retEdge = SVFUtil::dyn_cast<RetCFGEdge>(outEdge)) {
            reachability(retEdge, snk);
        } else {
            reachability(outEdge, snk);
        }
    }

    path.pop_back();
    visited.erase(curPair);
}

/// TODO: collect each path once this method is called during reachability analysis, and
/// Collect each program path from the entry to each assertion of the program. In this function,
/// you will need (1) add each path into the paths set; (2) call translatePath to convert each path into Z3 expressions.
/// Note that translatePath returns true if the path is feasible, false if the path is infeasible; (3) If a path is feasible,
/// you will need to call assertchecking to verify the assertion (which is the last ICFGNode of this path); (4) reset z3 solver.
void SSE::collectAndTranslatePath() {
    /// TODO: your code starts from here

    std::ostringstream oss;
    for (const ICFGEdge* edge : path) {
        oss << edge->getDstNode()->getId() << "->";
    }
    std::string pathStr = oss.str();
    if (!pathStr.empty()) {
        pathStr.resize(pathStr.size() - 2);
    }
    paths.insert(std::move(pathStr));

    if (translatePath(path)) {
        const ICFGNode* lastNode = path.back()->getDstNode();
        assertchecking(lastNode);
    }

    resetSolver();
}

/// TODO: Implement handling of function calls
void SSE::handleCall(const CallCFGEdge* calledge) {
    /// TODO: your code starts from here
    const ICFGNode* callNode = calledge->getSrcNode();

    for (const CallPE* pe : calledge->getCallPEs()) {
        expr rhs = getZ3Expr(pe->getRHSVarID());

        pushCallingCtx(callNode);
        expr lhs = getZ3Expr(pe->getLHSVarID());
        popCallingCtx();

        addToSolver(lhs == rhs);
    }

    pushCallingCtx(callNode);
}

/// TODO: Implement handling of function returns
void SSE::handleRet(const RetCFGEdge* retEdge) {
    /// TODO: your code starts from here

    expr rhs(getCtx());
    if (const RetPE* pe = retEdge->getRetPE()) {
        rhs = getZ3Expr(pe->getRHSVarID());
    }

    popCallingCtx();

    if (const RetPE* pe = retEdge->getRetPE()) {
        expr lhs = getZ3Expr(pe->getLHSVarID());
        addToSolver(lhs == rhs);
    }
}

/// TODO: Implement handling of branch statements inside a function
/// Return true if the path is feasible, false otherwise.
/// A given if/else branch on the ICFG looks like the following:
///             ICFGNode1 (condition %cmp)
///             1 /    \  0
///          ICFGNode2   ICFGNode3
/// edge->getCondition() returns the branch condition variable (%cmp) of type SVFValue* (for if/else) or a numeric condition variable (for switch).
/// Given the condition variable, you could obtain the SVFVar ID via "edge->getCondition()->getId()"
/// edge->getCondition() returns nullptr if this IntraCFGEdge is not a branch.
/// edge->getSuccessorCondValue() returns the actual condition value (1/0 for if/else) when this branch/IntraCFGEdge is executed. For example, the successorCondValue is 1 on the edge from ICFGNode1 to ICFGNode2, and 0 on the edge from ICFGNode1 to ICFGNode3
bool SSE::handleBranch(const IntraCFGEdge* edge) {
    /// TODO: your code starts from here
    const SVFValue* condValue = edge->getCondition();
    s32_t succValue = edge->getSuccessorCondValue();

    if (!condValue) {
        return true;
    }

    auto& ctx = getCtx();
    expr cond = getZ3Expr(condValue->getId());
    expr succ = ctx.int_val(succValue);

    solver &S = getSolver();
    S.push();
    addToSolver(cond == succ);
    z3::check_result res = S.check();
    S.pop();

    if (res == z3::unsat) {
        return false;
    } else {
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

    z3::context &z3ctx = getCtx();
    expr one = z3ctx.int_val(1);
    expr zero = z3ctx.int_val(0);

    for (const SVFStmt *stmt : dstNode->getSVFStmts())
    {
        if (const AddrStmt *addr = SVFUtil::dyn_cast<AddrStmt>(stmt))
        {
            // TODO: implement AddrStmt handler here
            expr obj = getMemObjAddress(addr->getRHSVarID());
            expr lhs = getZ3Expr(addr->getLHSVarID());
            addToSolver(obj == lhs);
        }
        else if (const CopyStmt *copy = SVFUtil::dyn_cast<CopyStmt>(stmt))
        {
            // TODO: implement CopyStmt handler her
            expr rhs = getZ3Expr(copy->getRHSVarID());
            expr lhs = getZ3Expr(copy->getLHSVarID());
            addToSolver(lhs == rhs);
        }
        else if (const LoadStmt *load = SVFUtil::dyn_cast<LoadStmt>(stmt))
        {
            // TODO: implement LoadStmt handler here
            expr lhs = getZ3Expr(load->getLHSVarID());
            expr rhs = getZ3Expr(load->getRHSVarID());
            addToSolver(lhs == z3Mgr->loadValue(rhs));
        }
        else if (const StoreStmt *store = SVFUtil::dyn_cast<StoreStmt>(stmt))
        {
            // TODO: implement StoreStmt handler here
            expr lhs = getZ3Expr(store->getLHSVarID());
            expr rhs = getZ3Expr(store->getRHSVarID());
            z3Mgr->storeValue(lhs, rhs);
        }
        else if (const GepStmt *gep = SVFUtil::dyn_cast<GepStmt>(stmt))
        {
            // TODO: implement GepStmt handler here
            expr basePtr = getZ3Expr(gep->getRHSVarID());
            s32_t offset = z3Mgr->getGepOffset(gep, callingCtx);
            expr res = getZ3Expr(gep->getLHSVarID());
            expr fieldAddr = z3Mgr->getGepObjAddress(basePtr, offset);
            addToSolver(res == fieldAddr);
        }
        else if (const CmpStmt *cmp = SVFUtil::dyn_cast<CmpStmt>(stmt))
        {
            // TODO: implement CmpStmt handler here
            expr op0 = getZ3Expr(cmp->getOpVarID(0));
            expr op1 = getZ3Expr(cmp->getOpVarID(1));
            expr res = getZ3Expr(cmp->getResID());

            expr cond(getCtx());

            switch (cmp->getPredicate())
            {
                case CmpStmt::ICMP_EQ:
                    cond = (op0 == op1);
                    break;
                case CmpStmt::ICMP_NE:
                    cond = (op0 != op1);
                    break;
                case CmpStmt::ICMP_UGT:
                case CmpStmt::ICMP_SGT:
                    cond = (op0 > op1);
                    break;
                case CmpStmt::ICMP_UGE:
                case CmpStmt::ICMP_SGE:
                    cond = (op0 >= op1);
                    break;
                case CmpStmt::ICMP_ULT:
                case CmpStmt::ICMP_SLT:
                    cond = (op0 < op1);
                    break;
                case CmpStmt::ICMP_ULE:
                case CmpStmt::ICMP_SLE:
                    cond = (op0 <= op1);
                    break;
                default:
                    assert(false && "unsupported integer predicate in CmpStmt");
            }

            addToSolver(res == ite(cond, one, zero));
        }
        else if (const BinaryOPStmt *binary = SVFUtil::dyn_cast<BinaryOPStmt>(stmt))
        {
            expr op0 = getZ3Expr(binary->getOpVarID(0));
            expr op1 = getZ3Expr(binary->getOpVarID(1));
            expr res = getZ3Expr(binary->getResID());

            auto solve = [&](const expr &e) { addToSolver(res == e); };

            switch (binary->getOpcode())
            {
                case BinaryOperator::Add:
                    solve(op0 + op1);
                    break;
                case BinaryOperator::Sub:
                    solve(op0 - op1);
                    break;
                case BinaryOperator::Mul:
                    solve(op0 * op1);
                    break;
                case BinaryOperator::SDiv:
                    solve(op0 / op1);
                    break;
                case BinaryOperator::SRem:
                    solve(op0 % op1);
                    break;
                case BinaryOperator::Xor:
                    solve(bv2int(int2bv(32, op0) ^ int2bv(32, op1), 1));
                    break;
                case BinaryOperator::And:
                    solve(bv2int(int2bv(32, op0) & int2bv(32, op1), 1));
                    break;
                case BinaryOperator::Or:
                    solve(bv2int(int2bv(32, op0) | int2bv(32, op1), 1));
                    break;
                case BinaryOperator::AShr:
                    solve(bv2int(ashr(int2bv(32, op0), int2bv(32, op1)), 1));
                    break;
                case BinaryOperator::Shl:
                    solve(bv2int(shl(int2bv(32, op0), int2bv(32, op1)), 1));
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
            addToSolver(res == ite(cond == one, tval, fval));
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
        const IntraCFGEdge startEdge(nullptr, const_cast<ICFGNode*>(src));
        for (const ICFGNode* sink : identifySinks()) {
            reachability(&startEdge, sink);
            resetSolver();
        }
    }
}