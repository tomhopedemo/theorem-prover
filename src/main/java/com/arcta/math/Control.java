package com.arcta.math;

import com.arcta.math.Def.State;
import com.arcta.math.Def.State.AND;
import com.arcta.math.Def.State.Guide;
import com.arcta.math.Def.State.Meta;
import com.arcta.math.Def.State.SET;

import java.io.IOException;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static com.arcta.math.Def.State.LOG.TRUE;
import static com.arcta.math.Parse.parseFile;
import static com.arcta.math.Util.*;
import static com.arcta.math.Util.Var.newVar;

class Control {

    static String NAME = "GRPXX";
    static int NUM_INSTANCES = 2;
    static boolean LINKED_INSTANCES = true;
    static long START = time();
    static String focus__debug = "";
    static int DEBUG_LEVEL = 0; //0 weak debug, 1 strong debug

    public static void main(String[] args) throws IOException {
        Def def = compile();
        while (def.size() < V && time() - START < V) {
            Logic.run(def);
            Build.run(def);
        }
        Theorem.run(def);
    }

    static Def compile() throws IOException {
        Map<String, Def> expanded = map();
        List<Def> defs = parseFile("/Users/tom/javas/math/pre.axiom");
        for (Def simpleDef : filter(defs, def -> !hasInstance(def.states(), State.Extend.class))) {
            expanded.put(simpleDef.name(), simpleDef);
        }
        Def def = expandDefRecurse(NAME, toMap(defs, d1 -> d1.name(), d1 -> d1), expanded, 0);
        def.unqs().forEach(u -> u.meta().prov(def.get(u.elt()).meta().prov()));
        Def combinedDef = new Def(NAME + "_" + NUM_INSTANCES, list(), list(), null);
        List<State> finalStates = list();

        SET set = def.identifyIndependentSet();
        List<String> newSetVariables = Util.list();
        for (int i = 0; i < NUM_INSTANCES; i++) {
            Def clonedDef = def.cloneDef(false);
            newSetVariables.add(clonedDef.getOldNewVarMap().get(set.var()));
            State newFinalState = clonedDef.getFinalState().cloneWithVar(newVar("*x" + i + "final", null));
            clonedDef.removeFinalState();
            clonedDef.addState(newFinalState);
            finalStates.add(newFinalState);
            combinedDef.addStates(clonedDef.getParamsAndStates());
        }

        combinedDef.addState(new AND(newVar("*@and", null), map(finalStates, s -> s.var()), new Meta("combined" + "-@")));
        if (!combinedDef.reach().contains(TRUE)) {
            combinedDef.addState(TRUE);
            combinedDef.newFinalAndState(list(TRUE.var()));
        }
        return combinedDef;
    }

    static Def expandDefRecurse(String name, Map<String, Def> rawMap, Map<String, Def> expandMap, int level) {
        final List<State> states = list();
        final Def def = rawMap.get(name);
        for (State state : def.states()) {
            if (!(state instanceof State.Extend extend)) {
                states.add(state);
                continue;
            }
            //3. expand def for extend
            Def expandDef = expandMap.get(extend.getExtendName());
            if (expandDef == null) {
                expandDef = expandDefRecurse(extend.getExtendName(), rawMap, expandMap, level + 1);
                expandMap.put(extend.getExtendName(), expandDef);
            }
            Def newExpandDef = expandDef.cloneDefForParser();
            newExpandDef.prependToProvenance(extend.meta().prov());
            pushVars(newExpandDef, extend.args());
            State lastState = last(newExpandDef.states()).cloneWithVar(extend.var());
            newExpandDef.removeFinalState();
            newExpandDef.addState(lastState);
            states.addAll(newExpandDef.states());
            pullGuidesFromParams(newExpandDef.params(), states, level);
        }
        return new Def(def.name(), copy(def.params()), states, null);
    }

    static void pullGuidesFromParams(List<State> params, List<State> states, int currentLevel) {
        for (State param : filter(params, p -> p.meta().hasGuides())) {
            for (State state : filter(states, s -> s.var().equals(param.var()))) {
                Set<Guide> newGuides = mapToSet(param.meta().getGuides(), t -> new Guide(copy(t.getVars()), t.getFixedIndices(), currentLevel, t.getFixedAlternative()));
                newGuides.addAll(state.meta().getGuides());
                Meta meta = state.meta().cloneMeta().setExcludeFromDefines(param.meta().shouldExcludeFromDefines() || state.meta().shouldExcludeFromDefines()).setGuides(newGuides);
                state.setMeta(meta);
            }
        }
    }

    static void pushVars(Def def, List<String> varsToInject) {
        Map<String, String> map = new HashMap<>();
        List<State> params = list();
        for (int i = 0; i < def.params().size(); i++) {
            map.put(def.params().get(i).var(), varsToInject.get(i));
        }
        for (State param : def.params()) {
            State newParam = param.cloneWithVar(map.get(param.var()));
            newParam.updateRefs(map);
            params.add(newParam);
        }
        def.setParams(params);
        def.states().forEach(s -> s.updateRefs(map));
    }
}