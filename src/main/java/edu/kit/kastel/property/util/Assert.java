package edu.kit.kastel.property.util;

public final class Assert {

    private Assert() { }

    public static void immutableFieldUnchanged(String immutableObject, String unchangedField) { }
    public static void immutableFieldEqual(String immutableObject0, String immutableObject1, String equalField0, String equalField1) { }

    public static void immutableFieldUnchanged_TranslationOnly(String immutableObject, String unchangedField) { }
    public static void immutableFieldEqual_TranslationOnly(String immutableObject0, String immutableObject1, String equalField0, String equalField1) { }

    public static void _assert(String a) { }
    public static void _assume(String a) { }

    public static void _verifast_assert(String a) { }
    public static void _verifast_open(String a) { }
    public static void _verifast_close(String a) { }

    public static void _verifast_assert_translationOnly(String a) { }
    public static void _verifast_open_translationOnly(String a) { }
    public static void _verifast_close_translationOnly(String a) { }
}
