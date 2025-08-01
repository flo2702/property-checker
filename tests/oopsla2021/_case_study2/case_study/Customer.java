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
package case_study;

import edu.kit.kastel.property.subchecker.lattice.case_study_qual.*;
import edu.kit.kastel.property.checker.qual.*;

public class Customer {
    
    public final String name;
    public final @Interval(min="14", max="150") int age;

    @JMLClause("ensures this.name == name && this.age == age")
    @JMLClause("assignable \\nothing")
    // :: error: inconsistent.constructor.type
    public @AgedOver(age="age") Customer(String name, @Interval(min="14", max="150") int age) {
        this.name = name;
        this.age = age;
    }

    @JMLClause("ensures \result.name == name && \result.age == 18")
    @JMLClause("assignable \\nothing")
    public static @AgedOver(age="18") Customer customer18(String name) {
        // :: error: return.type.incompatible
        return new Customer(name, 18);
    }

    @JMLClause("ensures \result.name == name && \result.age == 14")
    @JMLClause("assignable \\nothing")
    public static @AgedOver(age="14") Customer customer14(String name) {
        // :: error: return.type.incompatible
        return new Customer(name, 14);
    }
}
