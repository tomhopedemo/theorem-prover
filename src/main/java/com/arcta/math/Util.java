package com.arcta.math;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.io.Serializable;
import java.util.*;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

class Util {
    static NList split(String string, String delimiterRegex) {
        if (string == null) return null;
        List<String> list = new ArrayList<>(Arrays.asList(string.split(delimiterRegex)));
        return new NList(list, delimiterRegex);
    }

    static List<String> splitList(String string, String delimiterRegex) {
        NList split = split(string, delimiterRegex);
        return split == null ? null : split.getUnderlying();
    }

    static <T> List<T> except(Collection<T> collection, T except) {
        List<T> toReturn = toList(collection);
        toReturn.remove(except);
        return toReturn;
    }

    static <T> boolean find(Collection<T> collection, Predicate<T> predicate) {
        return collection.stream().filter(predicate).findAny().isPresent();
    }

    static <T> boolean containsAll(Collection<T> collection, T... objects) {
        for (T object : objects) {
            if (!collection.contains(object)) {
                return false;
            }
        }
        return true;
    }

    static boolean empty(String string) {
        return string == null || string.trim().length() == 0;
    }

    static List<String> prependEach(Collection<String> collection, String prepend) {
        if (empty(prepend) || empty(collection)) {
            return list();
        }
        List<String> list = list();
        for (String string : collection) {
            if (string == null) {
                continue;
            }
            list.add(prepend + string);
        }
        return list;
    }

    static void sout(String string) {
        System.out.println(string);
    }

    static String substringRemoveFirst(String string) {
        if (string.length() == 0) {
            return "";
        } else {
            return string.substring(1);
        }
    }

    static Map<String, Long> timeMap = map();

    static long time() {
        return System.currentTimeMillis();
    }

    static long V = 10000;

    static void timeStart(String id) {
        Long startTime = timeMap.get(id);
        if (startTime != null) {
            throw new UnsupportedOperationException("timer already exists for " + id);
        }
        timeMap.put(id, System.currentTimeMillis());
    }

    static long timeEnd(String id) {
        Long startTime = timeMap.get(id);
        if (startTime == null) {
            throw new UnsupportedOperationException("timer does not exist for " + id);
        }
        timeMap.remove(id);
        return System.currentTimeMillis() - startTime;
    }

    static void timeStart() {
        timeStart(Thread.currentThread().getStackTrace()[2].getMethodName());
    }

    static long timeEnd() {
        return timeEnd(Thread.currentThread().getStackTrace()[2].getMethodName());
    }

    static boolean coinflip() {
        return new Random().nextInt(2) > 0;
    }

    static boolean empty(Collection collection) {
        return (collection == null || collection.size() == 0 || (collection.size() == 1 && collection.iterator().next() == null));
    }

    static <T, U> HashMap<T, U> map() {
        return new HashMap<>();
    }

    static <E> Set<E> set() {
        return new HashSet<>();
    }

    static <T, U> MSet<T, U> mset() {
        return new MSet<>();
    }

    static <T> T random(Collection<T> collection) {
        return size(collection) == 0 ? null : toList(collection).get(new Random().nextInt(collection.size()));
    }

    static <T> Set<T> diffSet(Collection<T> in_a, Collection<T> not_in_b) {
        List<T> diff = diffList(in_a, not_in_b);
        if (empty(diff)) return null;
        return new HashSet<>(diff);
    }

    static <T> List<T> diffList(Collection<T> in_a, Collection<T> not_in_b) {
        Collection<T> a = in_a;
        Collection<T> b = not_in_b;
        List<T> to_return = list();
        if (empty(a)) return to_return;
        to_return.addAll(a);
        if (empty(b)) return to_return;
        to_return.removeAll(b);
        return to_return;
    }

    static <T> boolean diff(Collection<T> in_a, Collection<T> not_in_b) {
        return !empty(diffList(in_a, not_in_b));
    }

    static String string(Collection collection, String delimiter) {
        if (collection == null) {
            return null;
        }
        return out(collection, delimiter);
    }

    static <T> String out(Collection<T> collection, String separator) {
        StringBuilder sb = new StringBuilder();
        for (T object : collection) {
            if (object != null) {
                String str = object.toString();
                if (str != null) {
                    sb.append(str);
                }
            }
            sb.append(separator);
        }
        return substringRemoveLast(sb, separator.length());
    }

    static String substringRemoveLast(StringBuilder sb, Integer numToRemove) {
        if (sb.length() == 0 || numToRemove >= sb.length()) return "";
        return sb.substring(0, sb.length() - numToRemove);
    }

    static String safe(String value) {
        return value == null ? "" : value;
    }

    static <T> List<T> safe(List<T> a) {
        return empty(a) ? list() : a;
    }

    static <E> ArrayList<E> list(E... objects) {
        ArrayList<E> objectsList = new ArrayList<>();
        for (E object : objects) {
            objectsList.add(object);
        }
        return objectsList;
    }

    static <T> List<T> union(Collection<T> a, Collection<T> b) {
        List<T> union = list();
        if (!empty(a)) {
            union.addAll(a);
        }
        if (!empty(b)) {
            union.addAll(b);
        }
        return union;
    }

    static <T> T get(List<T> list, int index) {
        if (empty(list) || index >= list.size() || index == -1) {
            return null;
        }
        return list.get(index);
    }

    static int size(Collection collection) {
        if (collection == null) {
            return 0;
        }
        return collection.size();
    }

    static <T> List<T> sublist(List<T> list, int fromInc, int toExc) {
        if (list == null) {
            return null;
        }
        if (list.size() == 0 || fromInc >= list.size()) {
            return list();
        }
        List<T> sublist = list.subList(fromInc, Math.min(toExc, list.size()));
        return new ArrayList<>(sublist);
    }

    static <T> T last(List<T> collection) {
        if (empty(collection)) return null;
        return collection.get(collection.size() - 1);
    }

    static <T> List<T> toList(Collection<T> set) {
        return set == null ? null : new ArrayList<>(set);
    }

    static <T> List<T> copy(List<T> list) {
        return list == null ? null : new ArrayList<>(list);
    }

    static boolean hasInstance(Collection collection, Class clazz) {
        for (Object o : collection) {
            if (clazz.equals(o.getClass())) {
                return true;
            }
        }
        return false;
    }

    static <T> List<T> distinct(List<T> list) {
        return new ArrayList<>(new LinkedHashSet<>(list));
    }

    static <T> void addAll(Collection<T> existing, Collection<T> newElements) {
        if (existing == null || newElements == null) {
            return;
        }
        existing.addAll(newElements);
    }

    static <T> List<T> immutable(List<T> collection) {
        return Collections.unmodifiableList(collection);
    }

    static <T> List<T> flatList(Object... objects) {
        List<T> list = list();
        for (Object object : objects) {
            if (object instanceof Collection) {
                list.addAll((Collection<T>) object);
            } else {
                list.add((T) object);
            }
        }
        return list;
    }

    static boolean intersection(Collection a, Collection b) {
        if (empty(a) || empty(b)) {
            return false;
        }
        for (Object o : a) {
            for (Object o1 : b) {
                if (o.equals(o1)) {
                    return true;
                }
            }
        }
        return false;
    }

    static <T> Set<T> safe(Set<T> a) {
        return empty(a) ? new HashSet<>() : a;
    }

    static <K, T> MapList<K, T> mapList() {
        return new MapList<>();
    }

    static String substringRemoveLast(String sb) {
        return sb.length() == 0 ? "" : sb.substring(0, sb.length() - 1);
    }

    static String removeInnerParentheses(String s) {
        char[] chars = s.toCharArray();
        for (int i = 0; i < chars.length - 3; i++) {
            if ('(' == chars[i] && '(' == chars[i + 1]) {
                for (int j = i; j < chars.length - 1; j++) {
                    if (')' == chars[j] && ')' == chars[j + 1]) {
                        int innerCount = 0;
                        for (int k = i + 2; k < j; k++) {
                            char e = chars[k];
                            if (')' == e) {
                                innerCount--;
                            }
                            if (innerCount < 0) {
                                break;
                            }
                        }
                        if (innerCount == 0) {
                            StringBuilder sb = new StringBuilder();
                            for (int l = 0; l < chars.length; l++) {
                                if (l == i + 1 || l == j + 1) {
                                } else {
                                    sb.append(chars[l]);
                                }
                            }
                            return sb.toString();
                        }
                    }
                }
            }
        }
        return s;
    }

    static String removeOuterParentheses(String s) {
        if (s.startsWith("(") && s.endsWith(")")) {
            int count = 0;
            for (char c : s.substring(s.length() - 1).toCharArray()) {
                if ('(' == c) {
                    count++;
                } else if (')' == c) {
                    count--;
                }
                if (count == 0) {
                    break;
                }
            }
            if (count != 0) {
                s = s.substring(1, s.length() - 1);
            }
        }
        return s;
    }

    static void write(String path, String valueToWrite) {
        synchronized (path) {
            File file = new File(path);
            if (file.exists()) {
                file.delete();
            }
            if (file.getParentFile() != null) {
                if (!file.getParentFile().exists()) {
                    file.getParentFile().mkdirs();
                }
            }
            PrintWriter out = null;
            try {
                out = new PrintWriter(path);
            } catch (FileNotFoundException e) {
                e.printStackTrace();
            }
            out.append(valueToWrite);
            out.close();
        }
    }

    static void write(String path, Collection<String> valueToWrite) {
        StringBuilder sb = new StringBuilder();
        for (String s : valueToWrite) {
            sb.append(s + "\n");
        }
        write(path, sb.toString());
    }

    static <T, U, V> Map<U, V> toMap(Collection<T> collection, Function<T, U> keyMapper, Function<T, V> valueMapper) {
        return collection.stream().collect(Collectors.toMap(keyMapper, valueMapper));
    }

    static <T> List<T> filter(Collection<T> collection, Predicate<T> predicate) {
        return collection.stream().filter(predicate).collect(Collectors.toList());
    }

    static <T> Set<T> filterToSet(Collection<T> collection, Predicate<T> predicate) {
        List<T> filter = filter(collection, predicate);
        return new LinkedHashSet<>(filter);
    }

    static <T> List<T> filterAsSet(Collection<T> collection, Predicate<T> predicate) {
        Set<T> filter = filterToSet(collection, predicate);
        return new ArrayList<>(filter);
    }

    static <T, U> List<U> filterAs(Collection<T> collection, Predicate<T> predicate, Class<U> clazz) {
        return collection.stream().filter(predicate).map(a -> (U) a).collect(Collectors.toList());
    }

    static <T, U> List<U> map(Collection<T> collection, Function<T, U> mapping) {
        return collection.stream().map(mapping).collect(Collectors.toList());
    }

    static <T, U> List<U> mapFilter(Collection<T> collection, Function<T, U> mapping, Predicate<U> predicate) {
        return collection.stream().map(mapping).filter(predicate).collect(Collectors.toList());
    }

    static <T, U> Set<U> mapToSet(Collection<T> collection, Function<T, U> mapping) {
        return collection.stream().map(mapping).collect(Collectors.toSet());
    }

    static boolean startsWith(String string, String prefix) {
        if (string == null) return false;
        return string.startsWith(prefix);
    }

    static class InstanceAuto {
        int integer = 0;

        String incrementAndGet() {
            integer = integer + 1;
            return String.valueOf(integer);
        }
    }

    static class M<A, B> implements Serializable {
        A a;
        B b;

        M(A a, B b) {
            this.a = a;
            this.b = b;
        }

        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            M<?, ?> multi = (M<?, ?>) o;
            if (!Objects.equals(a, multi.a)) return false;
            return Objects.equals(b, multi.b);
        }

        public int hashCode() {
            int result = a != null ? a.hashCode() : 0;
            result = 31 * result + (b != null ? b.hashCode() : 0);
            return result;
        }
    }

    static class MapList<K, T> {
        Map<K, ArrayList<T>> mapList;

        MapList() {
            this.mapList = map();
        }

        Set<K> keys() {
            return this.mapList.keySet();
        }

        int put(K key, T listElement) {
            mapList.putIfAbsent(key, list());
            mapList.get(key).add(listElement);
            return mapList.get(key).size();
        }

        List<T> get(K key) {
            return mapList.get(key);
        }
    }

    static class MapSet<K extends Comparable<? super K>, T> implements Serializable {
        Map<K, Set<T>> mapSet;

        MapSet() {
            this.mapSet = map();
        }

        void put(K key, T listElement) {
            mapSet.putIfAbsent(key, new HashSet<T>());
            mapSet.get(key).add(listElement);
        }

        Set<T> get(K key) {
            return mapSet.get(key);
        }
    }

    static class MSet<A, B> {
        Set<M<A, B>> set;

        MSet() {
            this.set = set();
        }

        void add(A a, B b) {
            this.set.add(new M<>(a, b));
        }

        Set<M<A, B>> get() {
            return this.set;
        }
    }

    static class NList {
        String splitDelimiter;
        List<String> underlying;

        List<String> getUnderlying() {
            return underlying;
        }

        NList(List<String> underlying, String splitDelimiter) {
            this.underlying = underlying;
            this.splitDelimiter = splitDelimiter;
        }

        String get(int index) {
            if (underlying.size() < index + 1) {
                return null;
            }
            return underlying.get(index);
        }

        String reconstruct(List<String> list) {
            String string;
            if (list == null) {
                string = null;
            } else if (splitDelimiter.equals("\\s+")) {
                string = string(list, " ");
            } else if (splitDelimiter.equals("\\(")) {
                string = string(list, "(");
            } else {
                string = string(list, splitDelimiter);
            }
            return string;
        }

        String reconstructExcept(int i) {
            if (underlying == null) {
                return null;
            }
            if (i >= underlying.size()) {
                return null;
            }
            List<String> sublist = sublist(0, i);
            if (i != underlying.size() - 1) {
                sublist.addAll(sublist(i + 1, underlying.size()));
            }
            return reconstruct(sublist);
        }

        String reconstructExceptEnd() {
            return reconstructExcept(underlying.size() - 1);
        }

        List<String> sublist(int start_index, int end_index__exclusive) {
            if (underlying.size() < start_index + 1) {
                return list();
            }
            return underlying.subList(start_index, Math.min(underlying.size(), end_index__exclusive));
        }
    }

    static class Var {
        static InstanceAuto globalInstanceAuto = new InstanceAuto();

        static String newVar(Def.State state, Def def) {
            return newVar(state.var(), def == null ? null : def.name());
        }

        static String newVar(String old, String dName) {
            String prefix;
            if (old.contains("-")) {
                if (dName == null && old.matches("\\*[A-Z]{5}.*")) {
                    prefix = split("*" + old.substring(7), "-").reconstructExceptEnd();
                } else {
                    prefix = split(old, "-").reconstructExceptEnd();
                }
            } else {
                prefix = "*" + (dName == null ? "" : dName + "-") + substringRemoveFirst(old);
            }
            return prefix + "-" + globalInstanceAuto.incrementAndGet();
        }

        static String construct(String dName) {
            return "*" + dName + "-" + globalInstanceAuto.incrementAndGet();
        }
    }
}