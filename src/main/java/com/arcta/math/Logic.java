package com.arcta.math;

import com.arcta.math.Def.State.*;

import java.util.*;

import static com.arcta.math.Def.State.LOG.TRUE;
import static com.arcta.math.Logic.LogicianType.DEDUCE;
import static com.arcta.math.Logic.LogicianType.REDUCE;
import static com.arcta.math.Theorem.VarOut.generateReverseOutMapComplete;
import static com.arcta.math.Util.*;
import static com.arcta.math.Util.Var.newVar;

class Logic {
    Def def;
    int reductionsLoopCount = 0, deductionsLoopCount = 0;

    Logic(Def def) {
        this.def = def;
    }

    List<Reduction> reductions_run_once = list(new D_0());
    List<Reduction> reductions_run_multiple = list(new D_1(), new D_2(), new D_3(), new D_4(), new D_5(), new D_6());
    List<Deduction> deductions = list(new E_1(), new E_2());

    static void run(Def def) {
        new Logic(def).run();
    }

    void run() {
        loop(REDUCE);
        loop(DEDUCE);
    }

    boolean runReductions(Collection<Reduction> reductions) {
        timeStart();
        boolean reduced = false;
        for (Reduction reduction : reductions) {
            reduced |= reduction.reduce();
        }
        long time = timeEnd();
        sout("INFO: " + time + "ms " + " reductions loop: " + reductionsLoopCount);
        return reduced;
    }

    boolean runDeductions() {
        timeStart();
        boolean deduced = false;
        for (Deduction deduction : deductions) {
            deduced |= deduction.deduce();
        }
        long time = timeEnd();
        sout("deductions loop: " + deductionsLoopCount + " ms: " + time);
        return deduced;
    }

    enum LogicianType {DEDUCE, REDUCE}

    void deduce() {
        loop(LogicianType.DEDUCE);
    }

    void reduce() {
        loop(LogicianType.REDUCE);
    }

    void loop(LogicianType type) {
        while (true) {
            if (type == REDUCE) {
                reductionsLoopCount++;
            } else {
                deductionsLoopCount++;
            }
            List<Reduction> reductions = reductionsLoopCount <= 1 ? union(reductions_run_once, reductions_run_multiple) : reductions_run_multiple;
            boolean updated = type == LogicianType.DEDUCE ? runDeductions() : runReductions(reductions);
            if (updated && reductionsLoopCount > 10 || deductionsLoopCount > 10) {
                throw new UnsupportedOperationException();
            }
            if (!updated) break;
        }
    }

    class D_0 extends Reduction {
        boolean reduce_internal() {
            return reduce_internal_single();
        }

        boolean reduce_internal_single() {
            int count = 0;
            List<Def.State> states = list();
            states.addAll(def.elts());
            states.addAll(def.alls());
            states.addAll(def.sets());
            Map<String, List<String>> varOuts = Theorem.VarOut.generateVarOutsMap(states, def);
            MapSet<String, Def.State> outStatesMap = generateReverseOutMapComplete(def, varOuts);
            for (Map.Entry<String, Set<Def.State>> outStatesEntry : outStatesMap.mapSet.entrySet()) {
                List<Def.State> elts = filter(outStatesEntry.getValue(), e -> !e.meta().isReduced());
                if (elts.size() >= 2) {
                    List<Def.State> eltlist = toList(elts);
                    Def.State elt = eltlist.get(0);
                    for (Def.State eltToMerge : eltlist.subList(1, eltlist.size())) {
                        def.updateStates(Map.of(eltToMerge.var(), elt.var()), elt.var());
                        eltToMerge.meta().setReduced(true);
                        count++;
                    }
                }
            }
            if (Control.DEBUG_LEVEL > 0) sout("DEBUG: D_0 merged " + count + " with same out");
            return count > 0;
        }
    }

    class D_1 extends Reduction {
        boolean reduce_internal() {
            boolean b = false;
            while (true) {
                boolean b1 = reduce_internal_single();
                b |= b1;
                if (!b1) break;
            }
            return b;
        }

        boolean reduce_internal_single() {
            List<String> eltOrAlls = map(def.reachExes(), exe -> exe.x());
            Map<String, Def.State> map = def.getVarToStateMap();
            for (EQL eql : def.reachEqls()) {
                List<String> vars = filterAsSet(eql.getEqlArgs(), arg -> !map.get(arg).meta().isReduced() && eltOrAlls.contains(arg));
                if (vars.size() < 2) {
                    continue;
                }
                for (int i = 0; i < vars.size(); i++) {
                    Def.State si = map.get(vars.get(i));
                    for (int j = i + 1; j < vars.size(); j++) {
                        Def.State sj = map.get(vars.get(j));
                        if (!sj.args().contains(si.var()) && !si.args().contains(sj.var())) {
                            def.updateStates(Map.of(sj.var(), si.var()), si.var());
                            sj.meta().setReduced(true);
                            eql.addEqlArgs(list(sj.var()));
                            return true;
                        }
                    }
                }
            }
            return false;
        }
    }

    class D_2 extends Reduction {
        boolean reduce_internal_single() {
            Set<String> removed = set();
            boolean b = false;
            Map<String, Def.State> map = def.getVarToStateMap();
            for (AND and1 : def.ands()) {
                if (removed.contains(and1.var())) continue;
                for (Def.State and2 : mapFilter(and1.getTruths(), t -> map.get(t), s -> s instanceof AND)) {
                    if (find(except(def.states(), and1), s -> s.args().contains(and2.var()))) {
                        continue;
                    }
                    and1.removeTruth(and2.var());
                    and1.addTruths(((AND) and2).getTruths());
                    def.removeState(and2.var());
                    removed.add(and2.var());
                    b = true;
                }
            }
            return b;
        }
    }

    class D_3 extends Reduction {
        boolean reduce_internal_single() {
            Map<String, String> replacementMap = map();
            Map<String, Def.State> map = def.getVarToStateMap();
            Map<NOT, NOT> notMap = map();
            Map<NOT, NOT> topLevelMap = map();
            for (NOT not : def.nots()) {
                if (map.get(not.getx()) instanceof NOT) {
                    notMap.put(not, ((NOT) map.get(not.getx())));
                }
            }
            for (NOT not : notMap.keySet()) {
                if (!notMap.containsValue(not)) {
                    topLevelMap.put(not, notMap.get(not));
                }
            }
            for (NOT not : topLevelMap.keySet()) {
                replacementMap.put(not.var(), topLevelMap.get(not).getx());
            }
            def.updateStates(replacementMap);
            for (NOT not : topLevelMap.keySet()) {
                def.removeState(not.var());
            }
            boolean updated = topLevelMap.size() > 0;
            return updated;
        }
    }

    class D_4 extends Reduction {
        boolean reduce_internal_single() {
            List<Def.State> reach = def.reach();
            Map<String, Def.State> map = def.getVarToStateMap();
            for (IMP imp : def.reachImps()) {
                if (reach.contains(map.get(imp.getTruthA()))) {
                    def.newFinalAndState(list(imp.getTruthB()));
                    def.removeState(imp.var());
                    def.updateStates(Map.of(imp.var(), imp.getTruthB()));
                    return true;
                }
            }
            return false;
        }
    }

    class D_5 extends Reduction {
        boolean reduce_internal_single() {
            List<String> elts = map(def.reachExes(), e -> e.x());
            List<EQL> eqls = filter(def.reachEqls(), e -> e.getEqlArgs().size() == 1);
            for (EQL eql : filter(eqls, eql -> elts.contains(eql.getEqlArgs().get(0)))) {
                def.removeState(eql.var());
                def.updateStates(Map.of(eql.var(), TRUE.var()));
                return true;
            }
            return false;
        }
    }

    class D_6 extends Reduction {
        boolean reduce_internal_single() {
            Set<String> removed = set();
            boolean b = false;
            List<EQL> eqls = def.reachEqls();
            for (EQL eql1 : filter(eqls, e -> !empty(e.getEqlArgs()))) {
                if (removed.contains(eql1.var())) continue;
                for (EQL eql2 : except(eqls, eql1)) {
                    if (removed.contains(eql2.var())) continue;
                    if (eql1.getSet().equals(eql2.getSet()) && new HashSet<>(eql1.getEqlArgs()).equals(new HashSet<>(eql2.getEqlArgs()))) {
                        def.removeState(eql2.var());
                        def.updateStates(Map.of(eql2.var(), eql1.var()));
                        removed.add(eql2.var());
                        b = true;
                    }
                }
            }
            return b;
        }
    }

    class E_1 extends Deduction {
        boolean deduce_internal_single() {
            boolean b = false;
            for (EQL eql1 : def.eqls()) {
                for (EQL eql2 : filter(def.reachEqls(), e -> !(e.var().equals(eql1.var()) && e.getSet().equals(eql1.getSet())) && intersection(e.getEqlArgs(), eql1.getEqlArgs()) && diff(e.getEqlArgs(), eql1.getEqlArgs()))) {
                    eql1.addEqlArgs(diffSet(eql2.getEqlArgs(), eql1.getEqlArgs()));
                    b = true;
                }
            }
            return b;
        }
    }

    class E_2 extends Deduction {
        boolean deduce_internal_single() {
            List<UNQ> unqs = list();
            Set<String> newUnqEltProvs = set();
            Set<String> existingUnqElts = mapToSet(def.reachUnqs(), unq -> unq.elt());
            List<EQL> eqlsReach = def.reachEqls();
            Set<String> reachExeUnderlyings = mapToSet(def.reachExes(), exe -> exe.x());
            for (ELT elt1 : filter(def.elts(), e -> reachExeUnderlyings.contains(e.var()) && empty(e.meta().getCopyOf()) && !e.meta().isInjected() && empty(e.getGenerators()) && !existingUnqElts.contains(e.var()))) {
                for (ELT elt2 : filter(def.elts(), e -> elt1.var().equals(e.meta().getCopyOf()) && reachExeUnderlyings.contains(e.var()) && !elt1.meta().isInjected())) {
                    if (find(eqlsReach, eql -> containsAll(eql.getEqlArgs(), elt1.var(), elt2.var()))) {
                        newUnqEltProvs.add(elt1.meta().prov());
                    }
                }
            }
            if (empty(newUnqEltProvs)) {
                return false;
            }
            for (String prov : newUnqEltProvs) {
                List<ELT> eltsWithProv = filter(def.elts(), s -> prov.equals(s.meta().prov()) && empty(s.meta().getCopyOf()));
                for (ELT elt : eltsWithProv) {
                    unqs.add(new UNQ(newVar("*unq", null), elt.var(), new Def.State.Meta(prov)));
                }
            }
            def.newFinalAndState(map(unqs, s -> s.var()));
            def.addStates(unqs);
            return true;
        }
    }

    abstract class Deduction {
        int internalLoopCount = 0;

        boolean deduce() {
            Util.timeStart();
            boolean b = deduce_internal();
            long time = timeEnd();
            if (Control.DEBUG_LEVEL > 0) sout("DEBUG: " + b + " lc: " + deductionsLoopCount + "/" + internalLoopCount + " - " + this.getClass().getSimpleName() + time + "ms");
            return b;
        }

        boolean deduce_internal() {
            internalLoopCount = 0;
            boolean b = false;
            while (true) {
                boolean b1 = deduce_internal_single();
                internalLoopCount++;
                b |= b1;
                if (!b1) break;
            }
            return b;
        }

        abstract boolean deduce_internal_single();
    }

    abstract class Reduction {
        int internalLoopCount = 0;

        boolean reduce() {
            Util.timeStart();
            boolean b = reduce_internal();
            long time = timeEnd();
            if (Control.DEBUG_LEVEL > 0) sout("DEBUG: " + b + " lc: " + reductionsLoopCount + "/" + internalLoopCount + " - " + this.getClass().getSimpleName() + " ms: " + time);
            return b;
        }

        boolean reduce_internal() {
            internalLoopCount = 0;
            boolean b = false;
            while (true) {
                boolean b1 = reduce_internal_single();
                internalLoopCount++;
                b |= b1;
                if (!b1) break;
            }
            return b;
        }

        abstract boolean reduce_internal_single();
    }
}