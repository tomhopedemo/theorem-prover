package math;

import java.io.IOException;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static math.Def.State.LOG.TRUE;
import static math.Parse.parseFile;
import static math.Util.*;
import static math.Util.Var.newVar;

public class Compiler {

    public Compiler() {
    }

    public Def compile(String name, int numInstances) throws IOException {
        Map<String, Def> expanded = map();
        List<Def> defs = parseFile("pre.axiom");
        for (Def simpleDef : filter(defs, def -> !hasInstance(def.states(), Def.State.Extend.class))) {
            expanded.put(simpleDef.name(), simpleDef);
        }
        Def def = expandDefRecurse(name, toMap(defs, d1 -> d1.name(), d1 -> d1), expanded, 0);
        def.unqs().forEach(u -> u.meta().prov(def.get(u.elt()).meta().prov()));
        Def combinedDef = new Def(name + "_" + numInstances, list(), list(), null);
        List<Def.State> finalStates = list();

        Def.State.SET set = def.identifyIndependentSet();
        List<String> newSetVariables = Util.list();
        for (int i = 0; i < numInstances; i++) {
            Def clonedDef = def.cloneDef(false);
            newSetVariables.add(clonedDef.getOldNewVarMap().get(set.var()));
            Def.State newFinalState = clonedDef.getFinalState().cloneWithVar(newVar("*x" + i + "final", null));
            clonedDef.removeFinalState();
            clonedDef.addState(newFinalState);
            finalStates.add(newFinalState);
            combinedDef.addStates(clonedDef.getParamsAndStates());
        }

        combinedDef.addState(new Def.State.AND(newVar("*@and", null), map(finalStates, s -> s.var()), new Def.State.Meta("combined" + "-@")));
        if (!combinedDef.reach().contains(TRUE)) {
            combinedDef.addState(TRUE);
            combinedDef.newFinalAndState(list(TRUE.var()));
        }
        return combinedDef;
    }

    private Def expandDefRecurse(String name, Map<String, Def> rawMap, Map<String, Def> expandMap, int level) {
        final List<Def.State> states = list();
        final Def def = rawMap.get(name);
        for (Def.State state : def.states()) {
            if (!(state instanceof Def.State.Extend extend)) {
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
            Def.State lastState = last(newExpandDef.states()).cloneWithVar(extend.var());
            newExpandDef.removeFinalState();
            newExpandDef.addState(lastState);
            states.addAll(newExpandDef.states());
            pullGuidesFromParams(newExpandDef.params(), states, level);
        }
        return new Def(def.name(), copy(def.params()), states, null);
    }

    private void pullGuidesFromParams(List<Def.State> params, List<Def.State> states, int currentLevel) {
        for (Def.State param : filter(params, p -> p.meta().hasGuides())) {
            for (Def.State state : filter(states, s -> s.var().equals(param.var()))) {
                Set<Def.State.Guide> newGuides = mapToSet(param.meta().getGuides(), t -> new Def.State.Guide(copy(t.getVars()), t.getFixedIndices(), currentLevel, t.getFixedAlternative()));
                newGuides.addAll(state.meta().getGuides());
                Def.State.Meta meta = state.meta().cloneMeta().setExcludeFromDefines(param.meta().shouldExcludeFromDefines() || state.meta().shouldExcludeFromDefines()).setGuides(newGuides);
                state.setMeta(meta);
            }
        }
    }

    private void pushVars(Def def, List<String> varsToInject) {
        Map<String, String> map = new HashMap<>();
        List<Def.State> params = list();
        for (int i = 0; i < def.params().size(); i++) {
            map.put(def.params().get(i).var(), varsToInject.get(i));
        }
        for (Def.State param : def.params()) {
            Def.State newParam = param.cloneWithVar(map.get(param.var()));
            newParam.updateRefs(map);
            params.add(newParam);
        }
        def.setParams(params);
        def.states().forEach(s -> s.updateRefs(map));
    }
}
