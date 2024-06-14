package com.arcta.math;

import com.arcta.math.Def.State.*;
import com.arcta.math.Util.MapSet;
import java.util.*;
import static com.arcta.math.Util.*;
import static com.arcta.math.Util.Var.newVar;
import static java.util.Collections.emptyList;

class Def {
    String name;
    List<State> params;
    List<State> states;

    List<State> params() {
        return copy(params);
    }

    String name() {
        return name;
    }

    Map<String, String> oldNewVarMap;
    Map<String, String> getOldNewVarMap() {
        return oldNewVarMap;
    }//optional mapping set when cloning

    Def(String name, List<State> ps, List<State> states, Map<String, String> oldNewVarMap) {
        this.name = name;
        this.params = copy(ps);
        this.states = copy(states);
        this.oldNewVarMap = oldNewVarMap;
    }

    State param(String var) {
        return params.stream().filter(p -> var.equals(p.var())).findFirst().orElse(null);
    }

    void setParams(List<State> params) {
        this.params = copy(params);
    }

    List<State> states() {
        return states;
    }

    int size(){
        return states().size();
    }

    State get(String var) {
        return states.stream().filter(s -> var.equals(s.var())).findFirst().orElseGet(() -> param(var));
    }

    void addParam(State param) {
        params.add(param);
    }

    void addStates(List<? extends State> states) {
        states.forEach(s -> addState(s));
    }

    void addState(State state){
        if (!isFinalState(state)) {
            this.states.add(state);
            return;
        }
        if (getFinalState() == null){
            this.states.add(state);
        } else {
            State updatedVarState = state.cloneWithVar(newVar("*exfinal", null));
            this.states.add(updatedVarState);
            newFinalAndState(list(updatedVarState.var()));
        }
    }
    List<State> getParamsAndStates(){
        return union(params, states);
    }
    <T> List<T> filterType(Class<T> clazz){
        return filterAs(states, s -> clazz.isInstance(s), clazz);
    }
    List<SET> sets(){
        return filterAs(getParamsAndStates(), s -> s instanceof SET, SET.class);
    }
    List<ELT> elts(){
        return filterAs(getParamsAndStates(), s -> s instanceof ELT, ELT.class);
    }
    List<NOT> nots(){
        return filterType(NOT.class);
    }
    List<AND> ands(){
        return filterType(AND.class);
    }
    List<EQL> eqls(){
        return filterType(EQL.class);
    }
    List<EXE> exes(){
        return filterType(EXE.class);
    }
    List<UNQ> unqs(){
        return filterType(UNQ.class);
    }
    List<ALL> alls(){
        return filterType(ALL.class);
    }
    Def getDeps(State state){
        MapSet<String, State> varToContainedStates = new MapSet<>();
        states.forEach(s -> s.args().forEach(a -> varToContainedStates.put(a, s)));
        return new Def(this.name(), list(), toList(getDepsRecurse(state, varToContainedStates, set())), null);
    }
    Set<State> getDepsRecurse(State state, MapSet<String, State> varToContainedStates, Set<State> deps){
        deps.add(state);
        for (State containedState : safe(diffSet(varToContainedStates.get(state.var()), deps))) {
            getDepsRecurse(containedState, varToContainedStates, deps);
        } return deps;
    }
    void removeFinalState(){
        states.remove(states.size() -1);
    }
    List<UNQ> reachUnqs() {
        return filterAs(reach(), t -> t instanceof UNQ, UNQ.class);
    }
    List<EQL> reachEqls() {
        return filterAs(reach(), t -> t instanceof EQL, EQL.class);
    }
    List<EXE> reachExes() {
        return filterAs(reach(), t -> t instanceof EXE, EXE.class);
    }
    List<IMP> reachImps() {
        return filterAs(reach(), t -> t instanceof IMP, IMP.class);
    }
    List<NOT> reachNots() {
        return filterAs(reach(), t -> t instanceof NOT, NOT.class);
    }
    List<NOT> reachNotExes(){
        return filter(reachNots(), not -> get(not.getx()) instanceof EXE);
    }
    List<NOT> reachNotEqls() {
        return filter(reachNots(), not -> get(not.getx()) instanceof EQL);
    }
    List<State> reach() {
        List<State> reachTruths = list();
        reachRecurse(reachTruths, getFinalState(), getVarToStateMap());
        return reachTruths;
    }
    void reachRecurse(List<State> reachTruths, State state, Map<String, State> varToState) {
        if (reachTruths.contains(state)) return;
        reachTruths.add(state);
        if (!(state instanceof AND)) return;
        ((AND) state).getTruths().forEach(t -> reachRecurse(reachTruths, varToState.get(t), varToState));
    }
    void removeState(String v){
        states.removeIf(s -> v.equals(s.var()));
    }
    Set<String> getIterants(State state, Map<String, State> varToStateMap){
        return getIterantsRecurse(state, varToStateMap, new LinkedHashSet<>(), 0);
    }
    Set<String> getIterantsRecurse(State state, Map<String, State> varStates, Set<String> iterants, int count){
        if (count > 20){ throw new UnsupportedOperationException();}
        if (state instanceof ALL){
            iterants.add(state.var());
        }
        for (String arg : state.args()) {
            getIterantsRecurse(varStates.get(arg), varStates, iterants, count + 1);
        }
        if (empty(iterants) && state instanceof ELT){
            iterants.add(state.var());
        }
        return iterants;
    }
    void updateStates(Map<String, String> oldNew){
        updateStates(oldNew, null);
    }

    Def updateStates(Map<String, String> oldNew, String injectedWithMeta){
        states.forEach(s -> s.updateRefs(oldNew, injectedWithMeta));
        return this;
    }

    Map<String, State> getVarToStateMap(){
        return toMap(states, s -> s.var(), s -> s);
    }

    State getFinalState(){
        List<State> finalStates = filter(this.states, s -> isFinalState(s));
        return Util.get(finalStates, 0);
    }

    boolean isFinalState(State state){
        return state.var().contains("@");
    }

    void prependToProvenance(String toPrepend) {
        states.forEach(s -> s.meta().prov(toPrepend + "&" + s.meta().prov()));
    }

    Def cloneDef(boolean isCopy){
        Map<String, String> oldNew = map();
        List<State> states = cloneStates(false, isCopy, states(), oldNew);
        return new Def(name(), list(), states, oldNew);
    }

    SET identifyIndependentSet(){
        Map<String,State> varToStateMap = getVarToStateMap();
        for (SET set : sets()) {
            if (getIterants(set, varToStateMap).size() == 0){
                return set;
            }
        }
        return null;
    }

    Def cloneDefForParser(){
        Map<String, String> map = map();
        List<State> params = cloneStates(true, false, params(), map);
        List<State> states = cloneStates(true, false, states(), map);
        return new Def(name(), params, states, map);
    }

    List<State> cloneStates(boolean includeName, boolean isCopy, List<State> states, Map<String,String> oldNew) {
        List<State> cloned = list();
        for (State state : states) {
            State newState = state.cloneWithVar(newVar(state, includeName ? this : null));
            if (isCopy){
                newState.meta().setCopyOf(state.var());
            }
            cloned.add(newState); oldNew.put(state.var(), newState.var());
        }
        cloned.forEach(s -> s.updateRefs(oldNew));
        return cloned;
    }

    Map<String, String> copyStateDepsAndAddToDef(State state) {
        Def clone = getDeps(state).cloneDef(true);
        addStates(clone.states()); return clone.getOldNewVarMap();
    }

    void newFinalAndState(Collection<String> additionalAndArgs){
        State finalState = getFinalState();
        State newFinalState = finalState.cloneWithVar(newVar("*exfinal", null));
        LinkedHashSet<String> andArgs = new LinkedHashSet<>(additionalAndArgs);
        if (newFinalState instanceof AND){
            andArgs.addAll(((AND) newFinalState).getTruths());
        } else {
            andArgs.add(newFinalState.var());
        }
        AND and = new AND(newVar("*@and", null), new ArrayList<>(andArgs), new State.Meta(name() + "-@"));
        removeState(finalState.var());
        if (!(newFinalState instanceof AND)) {
            this.states.add(newFinalState);
        }
        this.states.add(and);
    }
    abstract static class State {
        final String var; Meta meta; List<String> args;  //var immutable/final //immutable, can be reset in updateRefs, pullUpGuides //immutable but can be reset in updateRefs, addEqlArgs
        protected State(String var, List<String> args, Meta meta){
            this.var = var;
            this.meta = meta;
            this.args = args == null ? emptyList() : immutable(args);
            if (safe(args).contains(var)){
                throw new UnsupportedOperationException();
            }
        }
        String var() {
            return var;
        }
        List<String> args(){
            return args;
        }
        Meta meta() {
            return meta;
        }
        void setMeta(Meta meta) {
            this.meta = meta;
        }
        Meta cloneMeta(){
            return this.meta.cloneMeta();
        }
        abstract State cloneWithVar(String newVar);
        void updateRefs(Map<String, String> oldNew){
            updateRefs(oldNew, null);
        }
        void updateRefs(Map<String, String> oldNew, String injectedWithMeta){
            ArrayList<String> newArgs = new ArrayList<>(Collections.nCopies(args.size(), null));
            for (int i = 0; i < args.size(); i++) {
                String newArg = oldNew.get(args.get(i));
                if (newArg != null && !newArg.equals(args.get(i))) {
                    newArgs.set(i, newArg);
                    if (!empty(injectedWithMeta)){
                        this.meta().setInjectedWith(injectedWithMeta);
                    }
                } else {
                    newArgs.set(i, args.get(i));
                }
            }
            updateArgs(newArgs);
            boolean updated = false;
            Set<Guide> newGuides = set();
            List<String> newMetaOfs = this.meta.getOfs();
            if (!empty(this.meta.getGuides())){
                for (Guide guide : this.meta.getGuides()) {
                    Guide newGuide = guide.getMappedGuide(oldNew);
                    if (!guide.getVars().equals(newGuide.getVars())) {
                        updated = true;
                    }
                    newGuides.add(newGuide);
                }
            }
            if (!empty(this.meta.getOfs())) {
                newMetaOfs = list();
                boolean updateMetaOf = false;
                for (String metaOf : this.meta.getOfs()) {
                    String newMetaOf = oldNew.get(metaOf);
                    if (!empty(newMetaOf)){
                        newMetaOfs.add(newMetaOf);
                        updateMetaOf = true;
                    } else {
                        newMetaOfs.add(metaOf);
                    }
                }
                if (updateMetaOf){
                    updated = true;
                }
            }
            if (updated){
                this.meta = this.meta.cloneMeta().setOfs(newMetaOfs).setGuides(newGuides);
            }
        }
        protected void updateArgs(List<String> newArgs){
            this.args = immutable(newArgs);
            if (safe(args).contains(var)){
                throw new UnsupportedOperationException();
            }
        }
        public String toString() {
            Meta meta = meta();
            if (meta == null) return "";
            return meta.toString();
        }  //used for intellij debug console only

    interface Truth { }
    static class AEA extends State {
        AEA(String name, Meta meta){
            super(name, null, meta);
        }
        AEA cloneWithVar(String newVar){
            return new AEA(newVar, cloneMeta());
        }
    }
    static class ALL extends State {
        ALL(String name, String underlying, Meta meta){
            super(name, list(underlying), meta);
        }
        ALL cloneWithVar(String newVar){
            return new ALL(newVar, getUnderlying(), cloneMeta());
        }
        String getUnderlying(){
            return args.get(0);
        }
    }
    static class ELT extends State {

        int iterantsBeginIndex;
        ELT(String var, String set, List<String> generators, List<String> iterants, Meta meta) {
            super(var, flatList(set, generators, iterants), meta);
            iterantsBeginIndex = 1 + generators.size();
        }
        ELT cloneWithVar(String newVar){
            return new ELT(newVar, getUnderlying(), getGenerators(), getIterants(), cloneMeta());
        }
        String getUnderlying(){
            return this.args.get(0);
        }
        List<String> getGenerators(){
            return sublist(args, 1, iterantsBeginIndex);
        }
        List<String> getIterants(){
            return sublist(args, iterantsBeginIndex, args.size());
        }
    }

    static class SET extends State {
            int iterantsStartIndex;
        SET(String var, List<String> generators, List<String> additionalIterants, Meta meta) {
            super(var, union(generators, additionalIterants), meta);
            iterantsStartIndex = Util.size(generators);
        }
        SET cloneWithVar(String newVar){
            return new SET(newVar, getGenerators(), getAdditionalIterants(), cloneMeta());
        }
        List<String> getGenerators(){
            return sublist(args, 0, iterantsStartIndex);
        }
        List<String> getAdditionalIterants(){
            return sublist(args, iterantsStartIndex, args.size());}
        }

    static class AND extends State implements Truth {
        AND(String name, List<String> truths, Meta meta){
            super(name, truths, meta);
        }
        AND cloneWithVar(String newVar) {
            return new AND(newVar, getTruths(), cloneMeta());
        }
        List<String> getTruths(){
            return args;
        }
        void addTruths(Collection<String> truths) {
            updateArgs(distinct(union(this.args, truths)));
        }
        void removeTruth(String truth) {
            updateArgs(distinct(except(this.args, truth)));
        }
    }
    static class EQL extends State implements Truth {
        EQL(String name, String underlying, List<String> items, Meta meta){
            super(name, union(list(underlying), items), meta);
        }
        EQL cloneWithVar(String newVar){
            return new EQL(newVar, getSet(), getEqlArgs(), cloneMeta());
        }
        String getSet(){
            return args.get(0);
        }
        List<String> getEqlArgs(){
            return args.subList(1, args.size());
        }
        void addEqlArgs(Collection<String> eqlArgs) {
            updateArgs(union(args(), eqlArgs));
            cleanEqlArgs();
        }
        void cleanEqlArgs() {
            updateArgs(flatList(getSet(), distinct(getEqlArgs())));
        }
    }
    static class EXE extends State implements Truth {
        EXE(String var, String underlying, Meta meta) {
            super(var, list(underlying), meta);
        }
        EXE cloneWithVar(String newVar){
            return new EXE(newVar, x(), cloneMeta());
        }
        String x(){
            return args.get(0);
        }
    }
    static class Extend extends State implements Truth {
            String extendName;
        Extend(String var, String extendName, List<String> args, Meta meta) {
            super(var, args, meta);
            this.extendName = extendName;
        }
        Extend cloneWithVar(String newVar){
            return new Extend(newVar, this.extendName, this.args, cloneMeta());
        }
        String getExtendName(){
            return extendName;
        }
    }
    static class IMP extends State implements Truth {
        IMP(String name, String truth1, String truth2, Meta meta){
            super(name, list(truth1, truth2), meta);
        }
        IMP cloneWithVar(String newVar){
            return new IMP(newVar, getTruthA(), getTruthB(), cloneMeta());
        }
        String getTruthA(){
            return args.get(0);
        }
        String getTruthB(){
            return args.get(1);
        }
    }
    static class LOG extends State implements Truth  {
        final static LOG TRUE = new LOG("*TRUE", new Meta("LOGIC-TRUE"));
        final static LOG FALSE = new LOG("*FALSE", new Meta("LOGIC-FALSE"));
        LOG(String var, Meta meta) {
            super(var, null, meta);
        }
        State cloneWithVar(String newVar) {
            return this;
        }
    }
    static class NOT extends State implements Truth {
        NOT(String name, String underlying, Meta meta){
            super(name, list(underlying), meta);
        }
        NOT cloneWithVar(String newVar){
            return new NOT(newVar, getx(), cloneMeta());
        }
        String getx() {
            return args.get(0);
        }
    }
    static class UNQ extends State implements Truth {
        UNQ(String v, String elt, Meta meta) {
            super(v, list(elt), meta);
        }
        UNQ cloneWithVar(String newVar){
            return new UNQ(newVar, elt(), cloneMeta());
        }
        String elt(){
            return args.get(0);
        }
    }

    static class Meta {
            String singular = null;
            Set<Guide> guides = set();
            List<String> ofs = null;
            List<String> relationships = null;
            boolean excludeFromDefines = false;
            boolean isInteresting = false;
            String provenance;
            String injectedWith = null;
            boolean reduced = false;
            String copyOf = null;
        Meta setSingular(String singular){
            this.singular = singular;
            return this;
        }
        String getSingular() {
            return singular;
        }
        boolean hasSingular(){
            return !empty(singular);
        }
        boolean hasGuides(){
            return !empty(guides);
        }
        Set<Guide> getGuides(){
            return guides;
        }
        Meta setGuides(Set<Guide> guides){
            this.guides = new HashSet<>(guides);
            return this;
        }
        List<String> getOfs() {
            return ofs;
        }
        Meta setOfs(List<String> ofs) {
            this.ofs = copy(ofs);
            return this;
        }
        List<String> getRelationships() {
            return relationships;
        }
        Meta setRelations(List<String> relationships){
            this.relationships = copy(relationships);
            return this;
        }
        boolean shouldExcludeFromDefines(){
            return excludeFromDefines;
        }
        Meta setExcludeFromDefines(boolean shouldExcludeFromDefines) {
            this.excludeFromDefines = shouldExcludeFromDefines;
            return this;
        }
        Meta setInteresting(boolean interesting) {
            this.isInteresting = interesting;
            return this;
        }
        Meta prov(String provenance) {
            this.provenance = provenance;
            return this;
        }
        String prov(){
            return this.provenance;
        }
        Meta(String provenance){
            this.provenance = provenance;
        }
        Meta setInjectedWith(String injectedWith) {
            this.injectedWith = injectedWith;
            return this;
        }
        boolean isInjected() {
            return !empty(injectedWith);
        }
        boolean isReduced(){
            return reduced;
        }
        Meta setReduced(boolean reduced){
            this.reduced = reduced;
            return this;
        }
        Meta setCopyOf(String copyOf){
            this.copyOf = copyOf;
            return this;
        }
        boolean isCopy(){
            return !empty(this.copyOf);
        }
        String getCopyOf() {
            return this.copyOf;
        }
        public String toString() {
            return prov();
        }
        Meta cloneMeta(){
            return new Meta(this.provenance).setSingular(this.singular).setOfs(this.ofs).setRelations(this.relationships).setExcludeFromDefines(this.excludeFromDefines).setInteresting(this.isInteresting).setGuides(this.guides).setInjectedWith(this.injectedWith).setReduced(this.reduced).setCopyOf(this.copyOf);
        }
    }

        static class Guide {
            final List<Integer> fixedIndices;
            final List<String> vars;
            final String fixedAlternative; //to generalize later
            final int level; //-1 when parsed //0+ if from params via expander.

            public String toString(){
                return outForAxiom();
            }

            Guide(List<String> vars, List<Integer> fixedIndices, int level, String fixedAlternative){
                this.vars = vars;this.fixedIndices = new ArrayList<>(fixedIndices);
                this.level = level;
                this.fixedAlternative = fixedAlternative;
            }

            Guide(String rawGuide) {
                StringBuilder varPart = new StringBuilder();
                StringBuilder staticPart = new StringBuilder();
                boolean inParentheses = false;
                List<Integer> staticIndicesInVarsAndStaticParts = list();
                List<String> varsAndStaticParts = list();
                List<String> splitSlash = splitList(rawGuide, "/");
                for (char character : Util.get(splitSlash,0).toCharArray()) {
                    if (character == '{'){
                        if (staticPart.length() > 0){
                            varsAndStaticParts.add(staticPart.toString());
                            staticPart = new StringBuilder();
                            staticIndicesInVarsAndStaticParts.add(varsAndStaticParts.size() - 1);
                        }
                        inParentheses = true;
                    } else if (character == '}'){
                        if (varPart.length() > 0){
                            varsAndStaticParts.add("*" + varPart.toString()); //add the var - and kill the var part
                            varPart = new StringBuilder();
                        }
                        inParentheses = false;
                    } else {
                        if (inParentheses){
                            varPart.append(character);
                        } else {
                            staticPart.append(character);
                        }
                    }
                }
                if (staticPart.length() > 0){
                    varsAndStaticParts.add(staticPart.toString());
                    staticIndicesInVarsAndStaticParts.add(varsAndStaticParts.size() - 1);
                }
                this.vars = varsAndStaticParts;
                this.fixedIndices = staticIndicesInVarsAndStaticParts;
                this.level = -1;
                this.fixedAlternative = Util.get(splitSlash, 1);}
            String getFixedAlternative(){
                return fixedAlternative;
            }
            List<Integer> getFixedIndices() {
                return fixedIndices;
            }
            List<String> getVars() {
                return vars;
            }
            String asString() {
                return string(vars, "");
            }
            List<Guide> getMappedGuides(Map<String, List<String>> oldNew) {
                List<Guide> toReturn = list();
                List<List<String>> newVarsList = list();
                newVarsList.add(list());
                for (int i = 0; i < vars.size(); i++) {
                    String existing = vars.get(i);
                    if (fixedIndices.contains(i)){
                        for (List<String> newVars : newVarsList) {
                            newVars.add(existing);
                        }
                    } else {
                        List<String> newVarOptions = oldNew.get(existing);                 //1. map var index
                        if (Util.size(newVarOptions) == 0) {
                            for (List<String> newVars : newVarsList) {
                                newVars.add(existing);
                            }
                        } else if (Util.size(newVarOptions) == 1) {
                            for (List<String> newVars : newVarsList) {
                                newVars.add(newVarOptions.get(0));
                            }
                        } else {
                            List<List<String>> multipliedLists = list();
                            for (List<String> list : newVarsList) {
                                for (int j = 0; j < Util.size(newVarOptions); j++) {
                                    ArrayList<String> newVersion = new ArrayList<>(list);
                                    newVersion.add(newVarOptions.get(j));
                                    multipliedLists.add(newVersion);
                                }
                            }
                            newVarsList = multipliedLists;
                        }
                    }
                }
                for (List<String> strings : newVarsList) {
                    toReturn.add(new Guide(strings, fixedIndices, level, fixedAlternative));
                }
                return toReturn;
            }
            Guide getMappedGuide(Map<String, String> oldNew) {
                List<String> newVars = list();
                for (int i = 0; i < vars.size(); i++) {
                    String existing = vars.get(i);
                    if (fixedIndices.contains(i)){
                        newVars.add(existing);
                    } else {
                        newVars.add(oldNew.getOrDefault(existing, existing));
                    }
                }
                return new Guide(newVars, fixedIndices, level, fixedAlternative);}
            List<String> getRealVars(){
                List<String> toReturn = list();
                for (int i = 0; i < vars.size(); i++) {
                    if (!fixedIndices.contains(i)){
                        toReturn.add(vars.get(i));
                    }
                }
                return toReturn;
            }
            String outForAxiom() {
                StringBuilder sb = new StringBuilder();
                for (int i = 0; i < vars.size(); i++) {
                    sb.append(fixedIndices.contains(i) ? vars.get(i) : "{" + vars.get(i) + "}");
                }
                if (!empty(fixedAlternative)){
                    sb.append("/" + fixedAlternative);
                }
                return sb.toString();
            }
            public boolean equals(Object o) {
                if (this == o) return true;
                if (o == null || getClass() != o.getClass()) return false;
                Guide guide = (Guide) o;
                return Objects.equals(vars, guide.vars);
            }

            public int hashCode() {
                return Objects.hash(vars);
            }
        }
    }
}