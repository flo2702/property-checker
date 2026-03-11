/* This file is part of the Property Checker.
 * Copyright (c) 2021 -- present. Property Checker developers.
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details.
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 */
package edu.kit.kastel.property.util;

import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.Set;

public class UnorderedPair<T> {

    private final Set<T> set = new HashSet<>();

    public UnorderedPair(T first, T second) {
        set.add(first);
        set.add(second);
    }

    public UnorderedPair(Set<T> set) {
        if (set.size() > 2 || set.isEmpty()) {
            throw new IllegalArgumentException();
        }

        this.set.addAll(set);
    }

    @Override
    public boolean equals(Object obj) {
        if (obj instanceof UnorderedPair) {
            UnorderedPair<?> other = (UnorderedPair<?>) obj;
            return set.equals(other.set);
        } else {
            return false;
        }
    }

    @Override
    public int hashCode() {
        return set.hashCode();
    }

    @Override
    public String toString() {
        return set.toString();
    }

    public Set<T> toSet() {
        return Collections.unmodifiableSet(set);
    }

    public Pair<T, T> toOrderedPair(Comparator<T> comparator) {
        if (set.size() == 1) {
            T op = set.iterator().next();
            return Pair.of(op, op);
        } else {
            @SuppressWarnings("unchecked")
            T[] ops = (T[]) set.toArray();

            int order = comparator.compare(ops[0], ops[1]);

            if (order == 0) {
                throw new IllegalArgumentException();
            } else if (order > 0) {
                T temp = ops[1];
                ops[1] = ops[0];
                ops[0] = temp;
            }

            return Pair.of(ops[0], ops[1]);
        }
    }

    public Pair<T, T> toOrderedPair() {
        return toOrderedPair((a, b) -> a.hashCode() - b.hashCode());
    }
}
