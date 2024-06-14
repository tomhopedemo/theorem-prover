package com.arcta.math;
import com.arcta.math.Def.State;
import com.arcta.math.Def.State.*;
import java.io.File;
import java.io.IOException;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import static com.arcta.math.Util.*;
import static java.nio.file.Files.readAllLines;
class Parse {
    static List<Def> parseFile(String file) throws IOException {
        List<Def> defs = list();
        Def currentDef = null;
        List<String> lines = getFunctionalLines(readAllLines(new File(file).toPath()));
        for (String line : lines) {
            if (line.matches("^[\\~].*")) {
                currentDef = parseDefLine(line);
                defs.add(currentDef);
            } else {
                currentDef.addStates(parseStateOrStates(currentDef, line));
            }
        }
        return defs;
    }
    static Def parseDefLine(String line) {
        String name, paramsRaw;
        if (line.contains("(")) {
            name = substringRemoveFirst(line.split("\\(")[0]);
            paramsRaw = substringRemoveLast(split(line, "\\(").reconstructExcept(0).trim());
        } else {
            name = substringRemoveFirst(line);
            paramsRaw = "";
        }
        Def def = new Def(name, list(), list(), null);
        List<String> params = list();
        StringBuilder param = new StringBuilder();
        boolean inMeta = false;
        for (int i = 0; i < paramsRaw.length(); i++) {
            char c = paramsRaw.charAt(i);
            if (c == '[') {
                inMeta = true;
            }
            if (c == ',' && !inMeta) {
                params.add(param.toString());
                param = new StringBuilder();
                continue;
            }
            if (c == ']') {
                inMeta = false;
            }
            param.append(c);
        }
        if (!empty(param.toString())) {
            params.add(param.toString());
        }
        params.forEach(p1 -> def.addParam(parseStateOrStates(def, p1).get(0)));
        return def;
    }
    static List<String> getFunctionalLines(List<String> read) {
        return read.stream().map(s -> split(s, "//").get(0)).filter(s -> !empty(s)) .map(s -> s.replaceAll("\\s+", "")).filter(s -> !empty(s)).collect(Collectors.toList());
    }
    static List<State> parseStateOrStates(Def def, String line) {
        List<String> split = splitList(line, ":");
        String varRaw = splitList(split.get(0), "\\[").get(0);
        String var = "*" + varRaw;
        List<State> states = list();
        Meta meta = parseMeta(line, varRaw, def);
        if (safe(get(split, 1)).trim().endsWith(")")) {
            states.add(parseExtend(line, var, meta));
        } else if (line.endsWith(":") || split.size() == 1 || CLASSIC_TYPES.contains(get(split, 1))) {
            states.addAll(parseClassic(def, line, var, meta));
        } else {
            List<String> splitLeftAngle = splitList(line, "\\<");
            List<String> iterants = parseReferenceIterants(get(splitLeftAngle, 1));
            String lhs = get(splitLeftAngle, 0);
            String v1 = "*" + split(lhs, ":").get(1);
            if (def.get(v1) instanceof SET) {
                List<String> lhsList = splitList(lhs, ":");
                List<String> argList = sublist(lhsList, 2, lhsList.size());
                states.add(new ELT(var, v1, prependEach(argList, "*"), iterants, meta));
            } else {
                throw new UnsupportedOperationException();
            }
        }
        return states;
    }
    static Meta parseMeta(String line, String rawVar, Def def) {
        List<String> metasRaw;         //1. Construct Raw Metas
        List<String> varMetasRawList = splitList(split(line, ":").get(0), "\\[");
        if (varMetasRawList.size() == 1) {
            metasRaw = list();
        } else {
            String metasRawString = split(varMetasRawList.get(1), "\\]").get(0);
            metasRaw = splitList(metasRawString, "\\|");
        }
        String metaSingular = get(metasRaw, 0); //e.g. binary__operation
        String guidesRaw = get(metasRaw, 1); //e.g.• or {a}{f}{b}
        String metaOfsRaw = get(metasRaw, 2);//e.g. G
        String metaRelationsRaw = get(metasRaw, 3); //e.g. on
        String excludeFromDefinesRaw = get(metasRaw, 4); //e.g. !
        String isInterestingRaw = get(metasRaw, 5); //e.g. !
        String originalProvenance = get(metasRaw, 6); //e.g. *X
        if (empty(originalProvenance)) {
            originalProvenance = def.name() + "-" + rawVar;
        }
        List<String> metaOfs = empty(metaOfsRaw) ? list() : prependEach(splitList(metaOfsRaw, ","), "*");
        List<String> metaRelations = empty(metaRelationsRaw) ? list() : splitList(metaRelationsRaw, ",");
        Set<State.Guide> guides = set();
        if (!empty(guidesRaw)) {
            for (String guideRaw : splitList(guidesRaw, ",")) {
                guides.add(new State.Guide(guideRaw));
            }
        }
        return new Meta(originalProvenance).setSingular(metaSingular).setOfs(metaOfs).setRelations(metaRelations).setGuides(guides).setExcludeFromDefines("!".equals(excludeFromDefinesRaw)).setInteresting("!".equals(isInterestingRaw));}
    static List<State> parseClassic(Def def, String line, String var, Meta meta) {
        String type = parseClassicType(line);  //1. Parse Type
        List<String> splitLine = splitList(line, ":"); //2. Parse Args
        List<String> argList = sublist(splitLine, 2, splitLine.size());
        List<String> args = prependEach(argList, "*"); List<State> stated = list();
        if ("SET".equals(type)) {stated.add(new SET(var, args, null, meta));}
        else if ("SET_IMPLIED".equals(type)) {stated.add(new SET(var, null, args, meta));}
        else if ("EQL".equals(type)) {stated.add(new EQL(var, args.get(0), args.subList(1, args.size()), meta));}
        else if ("NOT".equals(type)) {stated.add(new NOT(var, args.get(0), meta));}
        else if ("IMP".equals(type)) {stated.add(new IMP(var, args.get(0), args.get(1), meta));}
        else if ("AEA".equals(type)) {stated.add(new AEA(var, meta));}
        else if ("EXE".equals(type)) {stated.addAll(parseExe(var, args, meta, def.name()));}
        else if ("UNQ".equals(type)) {stated.add(new UNQ(var, args.get(0), meta));}
        else if ("AND".equals(type)) {stated.add(new AND(var, args, meta));}
        else if ("OR".equals(type)) {stated.addAll(parseOr(var, meta, args, def.name()));}
        else if ("NEQ".equals(type)){stated.addAll(parseNeq(var, meta, args, def.name()));}
        else if ("IFF".equals(type)){stated.addAll(parseIff(var, meta, args, def.name()));}
        else if ("NEX".equals(type)){stated.addAll(parseNex(var, meta, args, def.name()));}
        else if ("ALL".equals(type)) {stated.addAll(parseAll(var, meta, args));}
        else if ("ELT".equals(type)){stated.add(parseElt(line, var, meta));}
        else if ("LOG".equals(type)){stated.add("*TRUE".equals(var) ? LOG.TRUE : LOG.FALSE);}
        else {
            throw new UnsupportedOperationException("not a known classictype");
        }
        return stated;}
    static State parseElt(String line, String var, Meta meta) {
        List<String> splitLeftAngle = splitList(line, "\\<");
        List<String> iterants = parseReferenceIterants(get(splitLeftAngle, 1));
        List<String> lhsList = splitList(get(splitLeftAngle, 0), ":");
        List<String> rawArgList = sublist(lhsList, 3, lhsList.size());
        List<String> eltArgs = prependEach(rawArgList, "*");
        return new ELT(var, "*" + lhsList.get(2), eltArgs, iterants, meta);}
    static String parseClassicType(String line) {
        if (line.endsWith(":")) {
            return "AEA";
        } else if (size(splitList(line, ":")) == 1){
            return "SET_IMPLIED";
        } else {
            return get(splitList(line, ":"), 1);
        }
    }
    static List<State> parseNeq(String var, Meta meta, List<String> args, String dName){
        if (args.size() != 3){
            throw new UnsupportedOperationException("NEQ wrong num args");
        }
        EQL eql = new EQL(Util.Var.construct(dName), args.get(0), args.subList(1, args.size()), new Meta(meta.prov() + "/eql"));
        return list(eql, new NOT(var, eql.var(), meta));
    }
    static List<State> parseIff(String var, Meta meta, List<String> args, String dName){
        State imp1 = new IMP(Util.Var.construct(dName), args.get(0), args.get(1), new Meta(meta.prov() + "/1"));
        State imp2 = new IMP(Util.Var.construct(dName), args.get(1), args.get(0), new Meta(meta.prov() + "/2"));
        return list(imp1, imp2, new AND(var, list(imp1.var(), imp2.var()), meta));
    }
    static List<State> parseNex(String var, Meta meta, List<String> args, String dName){
        EXE exe = new EXE(Util.Var.construct(dName), args.get(0), new Meta(meta.prov() + "/exe"));
        return list(exe, new NOT(var, exe.var(), meta));
    }
    static List<State> parseAll(String var, Meta meta, List<String> args){
        List<State> alls = list(); List<String> vars = splitList(var, ",");
        for (String expandedVar : vars) {
            expandedVar = expandedVar.trim();
            Meta cloneMeta = meta.cloneMeta();
            if (vars.size() > 1) {
                cloneMeta.prov(meta.prov() + "/" + expandedVar);
            }
            if (!expandedVar.startsWith("*")){
                expandedVar = "*" + expandedVar;
            }
            alls.add(new ALL(expandedVar, args.get(0), cloneMeta));
        }
        return alls;
    }
    static List<State> parseOr(String var, Meta meta, List<String> args, String dName) {
        List<State> notStates = list();
        for (int i = 0; i < args.size(); i++) {
            notStates.add(new NOT(Util.Var.construct(dName), args.get(i), new Meta(meta.prov() + "/" + i)));
        }
        AND and = new AND(Util.Var.construct(dName), map(notStates, not -> not.var()), new Meta(meta.prov() + "/and"));
        return flatList(notStates, and, new NOT(var, and.var(), meta));
    }
    static List<State> parseExe(String var, List<String> args, Meta meta, String dName) {
        List<State> states = list();
        if (args.size() == 1){
            states.add(new EXE(var, args.get(0), meta));
        } else {
            for (String arg : args) {
                states.add(new EXE(Util.Var.construct(dName), arg, meta.cloneMeta().prov(meta.prov() + "/" + arg)));
            }
            states.add(new AND(var, map(states, exe -> exe.var()), meta));
        }
        return states;
    }
    static List<String> parseReferenceIterants(String iterantsRaw) {
        List<String> iterants = list();
        if (!empty(iterantsRaw)){
            iterants = prependEach(splitList(iterantsRaw, ":"), "*");
        }
        return iterants;
    }
    static State parseExtend(String line, String var, Meta meta) {
        String withoutVar = split(line, ":").reconstructExcept(0);
        List<String> rawExtendArgs = splitList(withoutVar.split("\\(")[1].split("\\)")[0], ",");
        return new Extend(var, split(withoutVar, "\\(").get(0), prependEach(rawExtendArgs, "*"), meta);
    }
    static final List<String> CLASSIC_TYPES = list("SET", "SET_IMPLIED", "ALL", "AEA", "LOG", "ELT", "EXE", "EQL", "IMP", "NOT", "AND", "UNQ", "OR", "IFF", "NEQ", "NEX");
}