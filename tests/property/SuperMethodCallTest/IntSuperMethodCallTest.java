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
import edu.kit.iti.checker.property.subchecker.lattice.qual.*;

class BaseClass {

    public void foo(@Interval(min="0", max="0") int arg) { }
}

class SubClass extends BaseClass {

    @Override
    public void foo(@Interval(min="0", max="1") int arg) { }
    
    public void bar() {
        foo(1);

        // :: error: argument.type.incompatible
        super.foo(1);
    }
}
