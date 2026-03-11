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

import java.util.Objects;

public class Pair<V1, V2> {

    public final V1 first;
    public final V2 second;

    private Pair(V1 first, V2 second) {
        this.first = first;
        this.second = second;
    }

    public static <T1, T2> Pair<T1, T2> of(T1 first, T2 second) {
        return new Pair<>(first, second);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }

        if (!(obj instanceof Pair)) {
            return false;
        }

        @SuppressWarnings("unchecked")
        Pair<V1, V2> other = (Pair<V1, V2>) obj;
        return Objects.equals(this.first, other.first) && Objects.equals(this.second, other.second);
    }

    private int hashCode = -1;

    @Override
    public int hashCode() {
        if (hashCode == -1) {
            hashCode = Objects.hash(first, second);
        }
        return hashCode;
    }

    @Override
    public String toString() {
        return "(" + first + ", " + second + ")";
    }
}
