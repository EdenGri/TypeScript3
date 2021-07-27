// L2-eval-box.ts
// L2 with mutation (set!) and env-box model
// Direct evaluation of letrec with mutation, define supports mutual recursion.

import { includes, map, reduce, repeat, zipWith } from "ramda";
import { isBoolExp, isCExp, isLitExp, isNumExp, isPrimOp, isStrExp, isVarRef,
         isAppExp, isDefineExp, isIfExp, isLetExp, isProcExp, Binding, VarDecl, CExp, Exp, IfExp, LetExp, ProcExp, Program,
         parseL21Exp, DefineExp, isSetExp, SetExp} from "./L21-ast";
import { applyEnv, makeExtEnv, Env, Store, setStore, extendStore, ExtEnv, applyStore, theGlobalEnv, globalEnvAddBinding, theStore } from "./L21-env-store";
import { isClosure, makeClosure, Closure, Value } from "./L21-value-store";
import { applyPrimitive } from "./evalPrimitive-store";
import { first, rest, isEmpty } from "../shared/list";
import { Result, bind, safe2, mapResult, makeFailure, makeOk } from "../shared/result";
import { parse as p } from "../shared/parser";
import { unbox } from "../shared/box";

// ========================================================
// Eval functions

const applicativeEval = (exp: CExp, env: Env): Result<Value> =>
    isNumExp(exp) ? makeOk(exp.val) :
    isBoolExp(exp) ? makeOk(exp.val) :
    isStrExp(exp) ? makeOk(exp.val) :
    isPrimOp(exp) ? makeOk(exp) :
    isVarRef(exp) ? bind(applyEnv(env,exp.var),(addr:number)=>applyStore(theStore,addr)) :
    isLitExp(exp) ? makeOk(exp.val as Value) :
    isIfExp(exp) ? evalIf(exp, env) :
    isProcExp(exp) ? evalProc(exp, env) :
    isLetExp(exp) ? evalLet(exp, env) :
    isAppExp(exp) ? safe2((proc: Value, args: Value[]) => applyProcedure(proc, args))
                        (applicativeEval(exp.rator, env), mapResult((rand: CExp) => applicativeEval(rand, env), exp.rands)) :
    isSetExp(exp) ? evalSetExp(exp,env) :
    exp;

export const isTrueValue = (x: Value): boolean =>
    ! (x === false);

const evalIf = (exp: IfExp, env: Env): Result<Value> =>
    bind(applicativeEval(exp.test, env),
         (test: Value) => isTrueValue(test) ? applicativeEval(exp.then, env) : applicativeEval(exp.alt, env));

const evalProc = (exp: ProcExp, env: Env): Result<Closure> =>
    makeOk(makeClosure(exp.args, exp.body, env));

// KEY: This procedure does NOT have an env parameter.
//      Instead we use the env of the closure.
const applyProcedure = (proc: Value, args: Value[]): Result<Value> =>
    isPrimOp(proc) ? applyPrimitive(proc, args) :
    isClosure(proc) ? applyClosure(proc, args) :
    makeFailure(`Bad procedure ${JSON.stringify(proc)}`);

const applyClosure = (proc: Closure, args: Value[]): Result<Value> => {
    const vars = map((v: VarDecl) => v.var, proc.params);
    const len = vars.length;
    const addresses: number[] = Array.from(Array(len)).map((_,i) => firstAvalable() + i );
    map((arg:Value)=> extendStore(theStore,arg),args);
    const newEnv: ExtEnv = makeExtEnv(vars, addresses, proc.env);
    return evalSequence(proc.body, newEnv);
}


const firstAvalable = (): number =>{
    const boxVals = unbox(theStore.vals);
    return boxVals.length;
}

// Evaluate a sequence of expressions (in a program)
export const evalSequence = (seq: Exp[], env: Env): Result<Value> =>
    isEmpty(seq) ? makeFailure("Empty program") :
    evalCExps(first(seq), rest(seq), env);
    
const evalCExps = (first: Exp, rest: Exp[], env: Env): Result<Value> =>
    isDefineExp(first) ? evalDefineExps(first, rest) :
    isCExp(first) && isEmpty(rest) ? applicativeEval(first, env) :
    isCExp(first) ? bind(applicativeEval(first, env), _ => evalSequence(rest, env)) :
    first;
//todo change arrow
const evalDefineExps = (def: DefineExp, exps: Exp[]): Result<Value> =>
    bind(applicativeEval(def.val,theGlobalEnv),
    (value : Value)=> {
        extendStore(theStore,value);
        const vals = map(unbox,theStore.vals[0]);
        const addr  = vals.indexOf(value);
        globalEnvAddBinding(def.var.var,addr);
        return evalCExps(first(exps),rest(exps),theGlobalEnv);
    });

// Main program
// L2-BOX @@ Use GE instead of empty-env
export const evalProgram = (program: Program): Result<Value> =>
    evalSequence(program.exps, theGlobalEnv);

export const evalParse = (s: string): Result<Value> =>
    bind(bind(p(s), parseL21Exp), (exp: Exp) => evalSequence([exp], theGlobalEnv));

// LET: Direct evaluation rule without syntax expansion
// compute the values, extend the env, eval the body.
const evalLet = (exp: LetExp, env: Env): Result<Value> => {
    const vals = mapResult((v: CExp) => applicativeEval(v, env), map((b: Binding) => b.val, exp.bindings));
    const vars = map((b: Binding) => b.var.var, exp.bindings);

    return bind(vals,(vals: Value[])=>{
        const len = vars.length;
        const addresses: number[] = Array.from(Array(len)).map((_,i) => firstAvalable() + i );
        const newEnv = makeExtEnv(vars, addresses, env);
        map((val:Value)=>extendStore(theStore,val),vals);
        return evalSequence(exp.body, newEnv);} );

}  



const evalSetExp = (set: SetExp, env: Env): Result<Value> =>{
    if(isEmpty(set.val)){
        return makeFailure("The value in Set! is empty");
    }
    const v = set.var.var;
    return safe2((value : Value, addr:number)=>makeOk(setStore(theStore , addr,value)))
                (applicativeEval(set.val,env),applyEnv(env,v));
}
    
