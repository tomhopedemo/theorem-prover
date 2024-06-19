package com.arcta.math;

import com.arcta.math.Def.State;
import com.arcta.math.Def.State.*;

import java.util.*;

import static com.arcta.math.Theorem.OutType.*;
import static com.arcta.math.Theorem.VarOut.generateReverseOutMap;
import static com.arcta.math.Util.*;

class Theorem {
    static Def currentDDebug = null;
    static String currentLemmaDebug = null;

    static void run(Def def) {
        currentDDebug = def;
        List<String> toWrite = list();
        toWrite.addAll(lemmas(def, EXISTENCES));
        toWrite.addAll(lemmas(def, UNIQUENESSES));
        toWrite.addAll(lemmas(def, EQUALITIES));
        toWrite.addAll(lemmas(def, IMPLICATIONS));
        toWrite.addAll(lemmas(def, NOT_EXISTENCES));
        toWrite.addAll(lemmas(def, NOT_EQUALITIES));
        sout(string(toWrite, " "));
        Util.write("/Users/tom/math/mathematician/combined/" + def.name() + "-2.txt", toWrite);
    }

    static List<String> lemmas(Def def, OutType outType) {
        final List<String> toWriteTotal = list();
        final LinkedHashMap<String, List<String>> lemmaOut = new LinkedHashMap<>();
        List<Reach> reach = outType.reach.get(def);
        if (empty(reach)) return toWriteTotal;
        Map<String, State> varToStateMap = def.getVarToStateMap();
        int lemmaNumber = 1;
        if (outType.equals(UNIQUENESSES) || outType.equals(EQUALITIES)) {
            for (int i = 0; i < reach.size(); i++) {
                String debug = outType.filePrefix.toUpperCase() + "/" + (i + 1) + "/" + lemmaNumber;
                currentLemmaDebug = debug;
                List<String> strings = outLemma(def, (State) reach.get(i), varToStateMap, outType, true);
                if (!empty(strings) && !lemmaOut.containsValue(strings)) {
                    lemmaOut.put("\n\n" + debug + "\n", strings);
                    lemmaNumber++;
                }
            }
        } else {
            List<String> strings = outLemma(def, (State) random(reach), varToStateMap, outType, true);
            if (!empty(strings)) {
                lemmaOut.put("\n\n" + "1/" + outType.filePrefix.toUpperCase() + "/" + (1) + "/" + lemmaNumber + "\n", strings);
            }
        }
        for (Map.Entry<String, List<String>> entry : lemmaOut.entrySet()) {
            toWriteTotal.add(entry.getKey());
            toWriteTotal.addAll(entry.getValue());
        }
        Util.write("/Users/tom/math/mathematician/" + def.name() + "/" + outType.filePrefix + "-" + def.name() + "-2.txt", toWriteTotal);
        return toWriteTotal;
    }

    static List<String> outLemma(Def def, State truth, Map<String, State> varToStateMap, OutType outType, boolean includeDefines) {
        final Set<State> toDefine = new LinkedHashSet<>();
        final List<State> statesToOut = list();
        final List<String> toWrite = list();
        final LinkedList<String> definesOutVars = new LinkedList<>();
        final Map<String, List<String>> outsMap = map();
        def.getIterants(truth, varToStateMap).forEach(i -> toDefine.add(def.get(i)));         //1. Get states to define
        if (outType.equals(OutType.UNIQUENESSES)) {
            toDefine.addAll(getToDefine(def, truth));
        } else if (outType.equals(OutType.EQUALITIES)) {
            toDefine.addAll(getToDefine(def, truth));
        } else if (outType.equals(EXISTENCES)) {
            if (def.get(((State.EXE) truth).x()).meta().shouldExcludeFromDefines()) {
                return null;
            }
            Set<State> toDefineExe = getToDefine(def, truth);
            if (!empty(toDefineExe) && hasInstance(toDefineExe, ALL.class)) {
                return null;
            }
            toDefine.addAll(toDefineExe);
        } else if (outType.equals(OutType.IMPLICATIONS)) {
            toDefine.addAll(getToDefine(def, def.get(((IMP) truth).getTruthA())));
            toDefine.addAll(getToDefine(def, def.get(((IMP) truth).getTruthB())));
        } else if (outType.equals(OutType.NOT_EXISTENCES)) {
            Set<State> toDefineExe = getToDefine(def, def.get(((NOT) truth).getx()));
            if (!empty(toDefineExe) && hasInstance(toDefineExe, ALL.class)) {
                return null;
            }
            toDefine.addAll(toDefineExe);
        } else if (outType.equals(OutType.NOT_EQUALITIES)) {
            toDefine.addAll(getToDefine(def, def.get(((NOT) truth).getx())));
        } else if (outType.equals(ELTS)) {
            if (def.get(((ELT) truth).getUnderlying()).meta().shouldExcludeFromDefines()) {
                return null;
            }
            Set<State> toDefineElt = getToDefine(def, truth);
            if (!empty(toDefineElt) && hasInstance(toDefineElt, ALL.class)) {
                return null;
            }
            toDefine.addAll(toDefineElt);
        }
        for (State state : toDefine) {
            getStatesRecurse(state, statesToOut, def);
        } //2. get states to out
        Map<String, List<String>> varOutsMap = VarOut.generateVarOutsMap(statesToOut, def);         //3. Generate var out map (values can sometimes be null for EQL run)
        Map<String, State> outStateMap = generateReverseOutMap(def, varOutsMap);         //4. and the reverse map also
        for (State state : toDefine) {
            List<String> findDefinesRecurseStartVars = varOutsMap.get(state.var());
            if (empty(findDefinesRecurseStartVars)) {
                continue;
            } //can be the case for EQL run
            for (String findDefinesRecurseStartVar : findDefinesRecurseStartVars) {
                if (!findDefinesRecurse(definesOutVars, outsMap, varOutsMap, outStateMap, findDefinesRecurseStartVar)) {
                    return null;
                }
            }
        }
        List<State> definesStates = filterDefinesOut(outStateMap, orderDefinesOut(definesOutVars, outStateMap, def));
        if (includeDefines) {
            addAll(toWrite, writeDefines(def, truth, varOutsMap, definesStates));
        }
        if (list(UNIQUENESSES, EQUALITIES, EXISTENCES, NOT_EXISTENCES, NOT_EQUALITIES).contains(outType)) {
            String out = outStateRecurse(truth, varOutsMap, def, false);
            if (out != null && out.contains("*")) {
                sout("");
            }
            if (empty(out)) {
                return null;
            } else {
                toWrite.add("\n" + (startsWith(last(toWrite), "For all") ? "" : "Then ") + out);
            }
        } else if (outType.equals(OutType.IMPLICATIONS)) {
            String outStateA = outStateRecurse(def.get(((IMP) truth).getTruthA()), varOutsMap, def, false);
            String outStateB = outStateRecurse(def.get(((IMP) truth).getTruthB()), varOutsMap, def, false);
            if (empty(outStateA) || empty(outStateB)) {
                return null;
            }
            toWrite.add("\nIf " + outStateA);
            toWrite.add("\nThen " + outStateB);
        } else if (outType.equals(ELTS)) {
            if (truth.meta().shouldExcludeFromDefines()) {
                return null;
            }
            String out = outStateRecurse(truth, varOutsMap, def, false);
            if (empty(out)) {
                return null;
            } else {
                if (includeDefines) {
                    toWrite.add("\n");
                }
                toWrite.add(out);
            }
        }
        return toWrite;
    }

    static List<State> filterDefinesOut(Map<String, State> outStateMap, List<String> definesOutVarsOrdering) {
        List<State> definesStates = list();
        for (String define : definesOutVarsOrdering) {
            State state = outStateMap.get(define);
            if (state != null) {
                definesStates.add(state);
            }
        }
        return definesStates;
    }

    static List<String> orderDefinesOut(LinkedList<String> definesOutVars, Map<String, State> outStateMap, Def def) {
        LinkedList<String> definesOutVarsOrdering = new LinkedList<>();
        List<String> outVarSection = list();
        List<String> alls = filter(definesOutVars, var -> outStateMap.get(var) instanceof ALL);
        List<State> allStmts = map(alls, a -> outStateMap.get(a));
        Map<String, List<String>> allToDeps = map();
        for (State all : allStmts) {
            Def deps = def.getDeps(all);
            List<String> depVars = map(deps.states(), s -> s.var());
            allToDeps.put(all.var(), depVars);
        }
        List<String> allsToAddAtTheEnd = list();
        for (String define : definesOutVars) {
            State state = outStateMap.get(define);
            if (state == null) {
                continue;
            }
            if (state instanceof ALL) {
                Collections.sort(outVarSection);
                definesOutVarsOrdering.addAll(outVarSection);
                allsToAddAtTheEnd.add(define);
                outVarSection = list();
            } else {
                outVarSection.add(define);
            }
        }
        Collections.sort(outVarSection);
        definesOutVarsOrdering.addAll(outVarSection);
        for (String all : allsToAddAtTheEnd) {
            List<String> deps = allToDeps.get(outStateMap.get(all).var());
            for (int i = 0; i < definesOutVarsOrdering.size(); i++) {
                if (deps.contains(outStateMap.get(definesOutVarsOrdering.get(i)).var())) {
                    definesOutVarsOrdering.add(i, all);
                    break;
                }
            }
        }
        return definesOutVarsOrdering;
    }

    static Set<State> getToDefine(Def def, State state) {
        final Set<State> toDefine = set();
        if (state instanceof UNQ) {
            toDefine.add(filter(def.elts(), e -> e.meta().prov().equals(state.meta().prov())).get(0));
        } else if (state instanceof EXE) {
            toDefine.add(def.get(((EXE) state).x()));
        } else if (state instanceof NOT) {
            toDefine.add(def.get(((NOT) state).getx()));
        } else if (state instanceof ELT) {
            toDefine.add(def.get(((ELT) state).getUnderlying()));
        } else if (state instanceof EQL) {
            for (String eqlArg : ((EQL) state).getEqlArgs()) {
                toDefine.add(def.get(eqlArg));
            }
        } else if (state instanceof AND) {
            for (String andArg : ((AND) state).getTruths()) {
                toDefine.add(def.get(andArg));
            }
        } else if (state instanceof IMP) {
            toDefine.add(def.get(((IMP) state).getTruthA()));
            toDefine.add(def.get(((IMP) state).getTruthB()));
        }
        return toDefine;
    }

    static List<String> writeDefines(Def def, State truth, Map<String, List<String>> varOutsMap, List<State> definesStates) {
        List<String> toWrite = list();
        State previousWrittenState = null;
        for (State state : definesStates) {
            if (state.meta().shouldExcludeFromDefines()) {
                continue;
            }
            if (truth instanceof EXE && state.var().equals(((EXE) truth).x())) {
                continue;
            }
            String mappedVarInstance = varOutsMap.get(state.var()).get(0);
            String singular = state.meta().getSingular();
            List<String> ofsMapped = map(safe(state.meta().getOfs()), of -> varOutsMap.get(of).get(0));
            String line;
            String of;
            List<String> ofSyntax = state.meta().getRelationships();
            if (empty(ofsMapped)) {
                of = "";
            } else if (empty(ofSyntax)) {
                of = " " + "of" + " " + string(ofsMapped, ",");
            } else if (size(ofSyntax) == 1) {
                of = " " + ofSyntax.get(0) + " " + string(ofsMapped, ",");
            } else if (ofsMapped.size() == 2 && ofSyntax.size() == 2) {
                of = " " + ofSyntax.get(0) + " " + ofsMapped.get(0) + " " + ofSyntax.get(1) + " " + ofsMapped.get(1);
            } else {
                throw new UnsupportedOperationException();
            }
            String typeQuantifier = empty(singular) ? "" : (list("a", "e", "i", "o", "u").contains((singular.substring(0, 1))) ? "an" : "a");
            if (def.params().contains(state) && state instanceof SET && !empty(ofsMapped)) {
                typeQuantifier = "the";
            }
            String type = empty(singular) ? "" : " be " + typeQuantifier + " " + singular.replace("__", " ");
            if (state instanceof ALL) {
                String underlying = varOutsMap.get(((ALL) state).getUnderlying()).get(0);
                if (previousWrittenState instanceof ALL && ((ALL) state).getUnderlying().equals(((ALL) previousWrittenState).getUnderlying())) {
                    line = last(toWrite);
                    toWrite.remove(toWrite.size() - 1);
                    String vars = line.substring(8, line.length() - (3 + underlying.length()));
                    line = "For all " + (vars + "," + mappedVarInstance) + " \u2208 " + underlying;
                } else {
                    line = "For all " + mappedVarInstance + " \u2208 " + underlying;
                }
            } else if (state instanceof ELT) {
                line = "Let " + mappedVarInstance + type + of;
            } else if (state instanceof SET) {
                line = "Let " + mappedVarInstance + type + of;
            } else {
                line = mappedVarInstance + " " + singular + of;
            }
            toWrite.add(line);
            previousWrittenState = state;
        }
        return toWrite;
    }

    static String outStateRecurse(State state, Map<String, List<String>> varOutsMap, Def def, boolean negation) {
        String out = null;
        if (state instanceof UNQ) {
            if (!negation) {
                List<ELT> eltsToDefine = filter(def.elts(), e -> e.meta().prov().contains(state.meta().prov()));
                out = string(varOutsMap.get(eltsToDefine.get(0).var()), " = ") + " is unique";
            }
        } else if (state instanceof EXE) {
            List<String> outs = varOutsMap.get(((EXE) state).x());
            if (!empty(outs)) {
                if (negation) {
                    out = outs.get(0) + " does not exist";
                } else {
                    out = string(outs, " = ") + " exists";
                }
            }
        } else if (state instanceof NOT) {
            if (!negation) {
                out = outStateRecurse(def.get(((NOT) state).getx()), varOutsMap, def, true);
            }
        } else if (state instanceof EQL) {
            if (negation) {
                List<String> outNotEquals = list();                 //only interested in negated eql outs w/ 2 args
                List<String> eqlArgs = ((EQL) state).getEqlArgs();
                if (eqlArgs.size() == 2) {
                    for (String eqlArg : eqlArgs) {
                        List<String> argOuts = varOutsMap.get(eqlArg);
                        if (!empty(argOuts)) {
                            outNotEquals.add(argOuts.get(0));
                        }
                    }//to generalize
                    out = string(outNotEquals, " \u2260 ");
                }
            } else {
                List<String> outEquals = list();
                for (String eqlArg : ((EQL) state).getEqlArgs()) {
                    List<String> argOuts = varOutsMap.get(eqlArg);
                    if (!empty(argOuts)) {
                        String argOut = argOuts.get(0);
                        if (!argOut.endsWith("-1")) {
                            outEquals.add(argOut);
                        }
                    }
                } //to generalize
                if (outEquals.size() >= 2) {
                    out = string(outEquals, " = ");
                }
            }
        } else if (state instanceof AND) {
            if (!negation) {
                List<String> andOuts = list();
                for (String truth : ((AND) state).getTruths()) {
                    String stateOut = outStateRecurse(def.get(truth), varOutsMap, def, false);
                    if (empty(stateOut)) {
                        return null;
                    }
                    andOuts.add(stateOut);
                }
                if (!empty(andOuts)) {
                    out = string(andOuts, " and ");
                }
            }
        } else if (state instanceof ELT) {
            if (!negation) {
                List<String> outs = varOutsMap.get(state.var());
                if (!empty(outs)) {
                    out = outs.get(0);
                }
            }
        }
        return out;
    }

    static boolean findDefinesRecurse(LinkedList<String> definesOutVars, Map<String, List<String>> outsMap, Map<String, List<String>> varOutsMap, Map<String, State> outStateMap, String out) {
        if (definesOutVars.contains(out)) {
            return true;
        }
        definesOutVars.add(out);
        State state = outStateMap.get(out);
        if (state == null) {
            return true;
        }
        if (!outsMap.containsKey(out)) {
            if (state instanceof ALL) {
                outsMap.put(out, new ArrayList<>(varOutsMap.get(((ALL) state).getUnderlying())));
            } else {
                List<String> ofsMapped = list();
                for (String of : safe(state.meta().getOfs())) {
                    ofsMapped.addAll(varOutsMap.get(of));
                }
                outsMap.put(out, ofsMapped);
                if (state.meta().hasGuides()) {
                    for (State.Guide guide : state.meta().getGuides()) {
                        List<String> realVars = guide.getRealVars();
                        List<String> mappedVars = list();
                        for (String realVar : realVars) {
                            List<String> mappedRealVar = varOutsMap.get(realVar);
                            if (empty(mappedRealVar)) {
                                return false;
                            }
                            mappedVars.addAll(mappedRealVar);
                        }
                        outsMap.get(out).addAll(mappedVars);
                    }
                }
            }
        }
        List<String> deps = outsMap.get(out);
        if (empty(deps)) {
            return true;
        }
        for (String depOut : deps) {
            if (!empty(depOut)) {
                findDefinesRecurse(definesOutVars, outsMap, varOutsMap, outStateMap, depOut);
            }
        }
        definesOutVars.remove(out);         //1. update the ordering of the defines out vars so that deps appear before this out.
        if (state instanceof ALL) {
            definesOutVars.add(out);
        } else {
            int maxIndex = -1;
            for (String dep : deps) {
                maxIndex = java.lang.Math.max(maxIndex, definesOutVars.indexOf(dep));
            }
            definesOutVars.add(maxIndex + 1, out);
        }
        return true;
    }

    static void getStatesRecurse(State state, List<State> states, Def def) {
        if (states.contains(state)) {
            return;
        }
        Set<String> referencedVars = set();
        if (state.meta().hasGuides()) {
            for (State.Guide guide : state.meta().getGuides()) {
                addAll(referencedVars, guide.getRealVars());
            }
        }
        addAll(referencedVars, state.meta().getOfs());
        if (state instanceof ALL) {
            referencedVars.add(((ALL) state).getUnderlying());
        }
        if (state instanceof EXE) {
            referencedVars.add(((EXE) state).x());
        }
        states.add(state);         //2. Add Out Var to Map
        for (String referencedVar : referencedVars) {
            getStatesRecurse(def.get(referencedVar), states, def);
        }
    }

    enum OutType {
        UNIQUENESSES("unqs", "Uniqueness", d -> d.reachUnqs()), EQUALITIES("eqls", "Equality", d -> d.reachEqls()), EXISTENCES("exes", "Existence", d -> d.reachExes()), NOT_EXISTENCES("notexes", "Non-Existence", d -> d.reachNotExes()), NOT_EQUALITIES("noteqls", "Non-Equality", d -> d.reachNotEqls()), IMPLICATIONS("imps", "Implication", d -> d.reachImps()), ELTS("elts", "Elts", d -> d.elts()); //debug
        String filePrefix;
        String title;
        Reach reach;

        OutType(String filePrefix, String title, Reach reach) {
            this.filePrefix = filePrefix;
            this.title = title;
            this.reach = reach;
        }

        interface Reach<T extends State> {
            List<T> get(Def def);
        }
    }

    static class Out {
        String var;
        Guide guide;
        State sourceState;

        Out(String var, Guide guide, State sourceState) {
            this.var = var;
            this.guide = guide;
            this.sourceState = sourceState;
        }

        String getVar() {
            return var;
        }

        Guide getGuide() {
            return guide;
        }

        void setVar(String var) {
            this.var = var;
        }

        boolean hasVar() {
            return !empty(var);
        }

        State getSourceState() {
            return sourceState;
        }

        public String toString() {
            StringBuilder sb = new StringBuilder();
            if (guide != null) {
                sb.append(guide);
            }
            sb.append(" | " + var);
            return sb.toString();
        }
    }

    static class VarOut {
        static <T extends State> Map<String, List<String>> generateVarOutsMap(List<T> states, Def def) {
            List<Out> guidedOuts = list();
            LinkedHashMap<State, List<Out>> stateOuts = new LinkedHashMap<>();
            Map<String, List<String>> oldNewVars = map();
            Map<String, List<String>> oldNew = new HashMap<>();
            for (T state : states) {
                List<Out> outs = list();
                if (state.meta().hasGuides()) {
                    for (Guide guide : state.meta().getGuides()) {
                        Out out = new Out(null, guide, state);
                        outs.add(out);
                        guidedOuts.add(out);
                    }
                } else if (state instanceof ALL) {
                    outs.add(new Out(createALLOutVarSimple(stateOuts), null, state));
                }
                stateOuts.put(state, outs);
            }
            for (Out guidedOutVar : guidedOuts) {
                updateGuidesRecurse(guidedOutVar, stateOuts, oldNewVars, def, new InstanceAuto());
            }
            for (Map.Entry<State, List<Out>> entry : stateOuts.entrySet()) {
                List<Out> value = entry.getValue();
                if (empty(value)) {
                    oldNew.put(entry.getKey().var(), null);
                } else {
                    List<String> outVars = list();
                    for (Out out : value) {
                        outVars.add(out.getVar());
                    }
                    oldNew.put(entry.getKey().var(), outVars);
                }
            }
            replaceSemicolonsWithCommas(oldNew);
            return oldNew;
        }

        static String createALLOutVarSimple(Map<State, List<Out>> stateOuts) {
            for (String outVar : list("x", "y", "z")) {
                if (noneMatch(stateOuts, outVar)) {
                    return outVar;
                }
            }
            return extendVar(stateOuts, "x");
        }

        static void updateGuidesRecurse(Out out, LinkedHashMap<State, List<Out>> stateOuts, Map<String, List<String>> oldNewVars, Def def, InstanceAuto count) {
            count.incrementAndGet();
            if (out.hasVar()) {
                List<String> newVars = oldNewVars.get(out.getSourceState().var());
                if (empty(newVars)) {
                    oldNewVars.put(out.getSourceState().var(), list(out.getVar()));
                } else {
                    oldNewVars.get(out.getSourceState().var()).add(out.getVar());
                }
                return;
            }
            Guide guide = out.getGuide();
            for (String guideRealVar : guide.getRealVars()) {         //perform a check that the var is different from what's calling it
                List<Out> guideRealVarOuts = stateOuts.get(def.get(guideRealVar));
                for (Out guideRealVarOut : guideRealVarOuts) {
                    if (!guideRealVarOut.equals(out)) {
                        updateGuidesRecurse(guideRealVarOut, stateOuts, oldNewVars, def, count);
                    }
                }
            }
            Guide newGuide = guide.getMappedGuides(oldNewVars).get(0);
            String newVarPrefix = newGuide.asString();
            String extendedVar;
            if (noneMatch(stateOuts, newVarPrefix) || map(def.reachUnqs(), u -> u.elt()).contains(out.getSourceState().var())) {
                extendedVar = newVarPrefix;
            } else if (!empty(newGuide.getFixedAlternative()) && noneMatch(stateOuts, newGuide.getFixedAlternative())) {
                extendedVar = newGuide.getFixedAlternative();
            } else {
                extendedVar = extendVar(stateOuts, newVarPrefix);
            }
            out.setVar(extendedVar);
            List<String> newVars = oldNewVars.get(out.getSourceState().var());
            if (empty(newVars)) {
                oldNewVars.put(out.getSourceState().var(), list(extendedVar));
            } else {
                oldNewVars.get(out.getSourceState().var()).add(extendedVar);
            }
        }

        static void replaceSemicolonsWithCommas(Map<String, List<String>> varOutsMap) {
            for (List<String> list : varOutsMap.values()) {
                if (!empty(list)) {
                    for (int i = 0; i < list.size(); i++) {
                        list.set(i, removeInnerParentheses(removeOuterParentheses(list.get(i).replace(";", ","))));
                    }
                }
            }
        }

        static boolean noneMatch(Map<State, List<Out>> stateOuts, String var) {
            for (List<Out> outList : stateOuts.values()) {
                for (Out out : outList) {
                    if (var.equals(out.getVar())) {
                        return false;
                    }
                }
            }
            return true;
        }

        static String extendVar(Map<State, List<Out>> stateOuts, String varPrefix) {
            int toAppend = 1;
            while (containsVar(stateOuts, varPrefix + "-" + toAppend)) {
                toAppend++;
            }
            return varPrefix + "-" + toAppend;
        }

        static boolean containsVar(Map<State, List<Out>> stateOuts, String var) {
            for (List<Out> outList : stateOuts.values()) {
                for (Out out : outList) {
                    if (var.equals(out.getVar())) {
                        return true;
                    }
                }
            }
            return false;
        }

        static Map<String, State> generateReverseOutMap(Def def, Map<String, List<String>> varOutsMap) {
            Map<String, State> outStateMap = map();
            for (String var : varOutsMap.keySet()) {
                State state = def.get(var);
                List<String> outVars = varOutsMap.get(var);
                if (!empty(outVars)) {
                    for (String outVar : outVars) {
                        outStateMap.put(outVar, state);
                    }
                }
            }
            return outStateMap;
        }

        static MapSet<String, State> generateReverseOutMapComplete(Def def, Map<String, List<String>> varOutsMap) {
            MapSet<String, State> outStateMap = new MapSet<>();
            for (String var : varOutsMap.keySet()) {
                State state = def.get(var);
                List<String> outVars = varOutsMap.get(var);
                if (!empty(outVars)) {
                    for (String outVar : outVars) {
                        outStateMap.put(outVar, state);
                    }
                }
            }
            return outStateMap;
        }
    }
}