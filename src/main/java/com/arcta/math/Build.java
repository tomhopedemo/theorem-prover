package com.arcta.math;

import com.arcta.math.Def.State.ALL;
import com.arcta.math.Def.State.ELT;
import com.arcta.math.Def.State.EXE;

import java.util.Collection;
import java.util.List;
import java.util.Map;

import static com.arcta.math.Control.focus__debug;
import static com.arcta.math.Util.*;

class Build {
    final List<Strategy> STRATS = list(new EltAllStrategy());
    Def def;

    Build(Def def) {
        this.def = def;
    }

    static void run(Def def) {
        new Build(def).executeRandom();
    }

    void executeRandom() {
        random(STRATS).executeRandom();
    }

    abstract class Strategy<A extends Def.State, B extends Def.State> {
        abstract Collection<M<A, B>> getCandidates();

        abstract void execute(M<A, B> t);

        void executeRandom() {
            Collection<M<A, B>> candidates = getCandidates();
            if (!empty(focus__debug) && coinflip()) {
                candidates = filterToSet(candidates, ab -> focus__debug.equals(ab.a.meta().prov()));
            }
            if (empty(candidates)) return;
            execute(random(candidates));
        }

        void inject(String eltOrAll, ALL all) {
            def.addStates(injectStateIntoAll(eltOrAll, all, def.getDeps(all)).states());
        }
    }

    class EltAllStrategy extends Strategy<ELT, ALL> {
        Collection<M<ELT, ALL>> getCandidates() {
            return getEltAlls().get();
        }

        void execute(M<ELT, ALL> eltAll) {
            ALL allToInjectInto;
            boolean copyingAll = false;
            String eltToInject;
            boolean copyingElt = false;
            if (!eltAll.b.meta().isCopy()) {
                allToInjectInto = (ALL) def.get(def.copyStateDepsAndAddToDef(eltAll.b).get(eltAll.b.var()));
                copyingAll = true;
            } else if (coinflip()) {
                allToInjectInto = (ALL) def.get(def.copyStateDepsAndAddToDef(eltAll.b).get(eltAll.b.var()));
                copyingAll = true;
            } else {
                allToInjectInto = eltAll.b;
            } //use existing all
            if (map(def.reachUnqs(), u -> u.elt()).contains(eltAll.a.var())) {
                eltToInject = eltAll.a.var();
            } else if (!eltAll.a.meta().isCopy()) {
                eltToInject = def.copyStateDepsAndAddToDef(eltAll.a).get(eltAll.a.var());
                copyingElt = true;
            } else if (coinflip()) {
                eltToInject = def.copyStateDepsAndAddToDef(eltAll.a).get(eltAll.a.var());
                copyingElt = true;
            } else {
                eltToInject = eltAll.a.var();
            }
            sout(this.getClass().getSimpleName() + " injecting: " + eltToInject + " " + (copyingElt ? "(copy)" : "") + " -> " + allToInjectInto.var() + (copyingAll ? "(copy)" : "") + " ... " + def.get(eltToInject).meta().prov() + " -> " + allToInjectInto.meta().prov());
            inject(eltToInject, allToInjectInto);
        }
    }

    class AllAllStrategy extends Strategy<ALL, ALL> {
        Collection<M<ALL, ALL>> getCandidates() {
            return filter(getAllAlls().get(), aa -> empty(aa.b.meta().getCopyOf()));
        }

        void execute(M<ALL, ALL> allAll) {
            inject(def.copyStateDepsAndAddToDef(allAll.a).get(allAll.a.var()), allAll.b);
        }
    }

    static Def injectStateIntoAll(String toInject, ALL all, Def allDeps) {
        Def clonedAllDeps = allDeps.cloneDef(false);
        String clonedAll = clonedAllDeps.getOldNewVarMap().get(all.var());
        clonedAllDeps.removeState(clonedAll);
        return clonedAllDeps.updateStates(Map.of(clonedAll, toInject), toInject);
    }

    MSet<ELT, ALL> getEltAlls() {
        MSet<ELT, ALL> eltAlls = mset();
        final List<ELT> elts = def.elts();
        final List<EXE> exes = def.exes();
        final List<ALL> alls = def.alls();
        final List<String> exeUnderlyings = map(exes, e -> e.x());
        for (ELT elt : filterToSet(elts, e -> exeUnderlyings.contains(e.var()))) {
            for (ALL all : alls) {
                if (all.getUnderlying().equals(elt.getUnderlying())) {
                    eltAlls.add(elt, all);
                }
            }
        }
        return eltAlls;
    }

    MSet<ALL, ALL> getAllAlls() {
        MSet<ALL, ALL> allAlls = mset();
        MapList<String, ALL> underlyingAlls = mapList();
        for (ALL a : def.alls()) {
            underlyingAlls.put(a.getUnderlying(), a);
        }
        for (String key : underlyingAlls.keys()) {
            Def.State state = def.get(key);
            if (!state.meta().hasSingular()) {
                continue;
            }
            List<ALL> alls = underlyingAlls.get(key);
            for (ALL all1 : alls) {
                for (ALL all2 : filter(except(alls, all1), a -> !empty(a.meta().getCopyOf()))) {
                    allAlls.add(all1, all2);
                }
            }
        }
        return allAlls;
    }
}