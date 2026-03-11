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
package edu.kit.kastel.property.lattice.parser;

import edu.kit.kastel.property.lattice.*;
import edu.kit.kastel.property.lattice.Bound.BoundType;
import edu.kit.kastel.property.subchecker.lattice.LatticeAnnotatedTypeFactory;
import edu.kit.kastel.property.util.ClassUtils;
import edu.kit.kastel.property.util.Pair;
import edu.kit.kastel.property.util.UnorderedPair;

import java.io.IOException;
import java.io.StreamTokenizer;
import java.io.StringReader;
import java.lang.annotation.Annotation;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

@SuppressWarnings("nls")
public final class LatticeParser {

    private LatticeAnnotatedTypeFactory factory;

    public LatticeParser(LatticeAnnotatedTypeFactory factory) {
        this.factory = factory;
    }

    public Lattice parse(String str) throws ParseException {
        StreamTokenizer tokenizer = new StreamTokenizer(new StringReader(str));
        tokenizer.ordinaryChar('+');
        tokenizer.ordinaryChar('-');
        tokenizer.ordinaryChar('*');
        tokenizer.ordinaryChar('/');
        tokenizer.ordinaryChar('(');
        tokenizer.ordinaryChar(')');
        tokenizer.ordinaryChar(':');
        tokenizer.ordinaryChar('<');
        tokenizer.ordinaryChar('>');
        tokenizer.ordinaryChar('=');

        tokenizer.ordinaryChar('.');
        tokenizer.wordChars('.', '.');
        tokenizer.wordChars('_', '_');
        tokenizer.wordChars('§', '§');

        tokenizer.commentChar('#');

        String ident = "default_ident";
        Map<String, PropertyAnnotationType> annotations = new HashMap<>();
        Map<Pair<String, String>, SubAnnotationRelation> relations = new HashMap<>();
        Map<UnorderedPair<String>, List<Bound>> meets = new HashMap<>();
        Map<UnorderedPair<String>, List<Bound>> joins = new HashMap<>();

        next(tokenizer);
        while(tokenizer.ttype != StreamTokenizer.TT_EOF) {
            switch(currentToken(tokenizer)) {
            case "ident":
                ident = parseIdent(tokenizer);
                break;
            case "annotation":
                PropertyAnnotationType annotation = parseAnnotation(tokenizer);
                annotations.put(annotation.getName(), annotation);
                break;
            case "relation":
                SubAnnotationRelation relation = parseRelation(tokenizer, annotations, relations);
                relations.put(
                        Pair.of(
                                relation.getSubAnnotationName(),
                                relation.getSuperAnnotationName()),
                        relation);
                break;
            case "join":
                Bound join = parseBound(BoundType.JOIN, tokenizer, annotations);
                if (!joins.containsKey(join.getOperandNames())) {
                    joins.put(join.getOperandNames(), new ArrayList<>());
                }
                joins.get(join.getOperandNames()).add(join);
                break;
            case "meet":
                Bound meet = parseBound(BoundType.MEET, tokenizer, annotations);
                if (!meets.containsKey(meet.getOperandNames())) {
                    meets.put(meet.getOperandNames(), new ArrayList<>());
                }
                meets.get(meet.getOperandNames()).add(meet);
                break;
            default:
                throw new ParseException("Unexpected token: " + currentToken(tokenizer));
            }

            next(tokenizer);
        }

        return new Lattice(factory, ident, annotations, relations, meets, joins);
    }

    private String parseIdent(StreamTokenizer tokenizer) throws ParseException {
        String ident = matchString(tokenizer);
        matchChar(tokenizer, ";");
        return ident;
    }

    private PropertyAnnotationType parseAnnotation(StreamTokenizer tokenizer) throws ParseException {
        String annotationName = matchString(tokenizer);
        matchChar(tokenizer, '(');

        List<PropertyAnnotationType.Parameter> parameters = new ArrayList<>();

        next(tokenizer);
        if (!currentToken(tokenizer).equals(")")) {
            tokenizer.pushBack();

            do {
                String typeName = matchString(tokenizer);
                String paramName = matchString(tokenizer);

                parameters.add(new PropertyAnnotationType.Parameter(
                        PropertyAnnotationType.ParameterType.valueOf(typeName.toUpperCase()),
                        paramName));

                matchChar(tokenizer, "),");
            } while (!currentToken(tokenizer).equals(")"));
        }

        String annotatedTypeName = matchString(tokenizer);

        matchChar(tokenizer, ":");
        matchChar(tokenizer, "<");
        matchChar(tokenizer, "=");
        matchChar(tokenizer, "=");
        matchChar(tokenizer, ">");

        String property = matchString(tokenizer);

        String precondition;
        next(tokenizer);
        String token = currentToken(tokenizer);
        if (token.equals("for")) {
            precondition = matchString(tokenizer);
        } else {
            precondition = "true";
            tokenizer.pushBack();
        }

        matchChar(tokenizer, ';');
        return new PropertyAnnotationType(
                ClassUtils.classForName(factory.getChecker().getQualPackage() + "." + annotationName, factory.getChecker()).asSubclass(Annotation.class),
        		ClassUtils.typeForName(annotatedTypeName, factory.getChecker()),
        		parameters,
        		property,
        		precondition);
    }

    private SubAnnotationRelation parseRelation(
            StreamTokenizer tokenizer,
            Map<String, PropertyAnnotationType> annotations,
            Map<Pair<String, String>, SubAnnotationRelation> relations) throws ParseException {
        PropertyAnnotation subAnnotation = parseInstantiatedAnnotation(tokenizer, annotations);

        matchChar(tokenizer, '<');
        matchChar(tokenizer, ':');

        PropertyAnnotation superAnnotation = parseInstantiatedAnnotation(tokenizer, annotations);

        matchChar(tokenizer, ":");
        matchChar(tokenizer, "<");
        matchChar(tokenizer, "=");
        matchChar(tokenizer, "=");
        matchChar(tokenizer, ">");

        String condition = matchString(tokenizer);

        matchChar(tokenizer, ';');

        String subAnnotationName = subAnnotation.getAnnotationType().getName();
        String superAnnotationName = superAnnotation.getAnnotationType().getName();

        if (relations.containsKey(Pair.of(subAnnotationName, superAnnotationName))) {
            throw new ParseException(
                    "Relation \"" + subAnnotationName + " :< " + superAnnotationName +
                    "\" defined already exists in line " + tokenizer.lineno());
        }

        return new SubAnnotationRelation(subAnnotation, superAnnotation, condition);
    }

    private Bound parseBound(BoundType boundType, StreamTokenizer tokenizer, Map<String, PropertyAnnotationType> annotations) throws ParseException {
        PropertyAnnotation annotation0 = parseInstantiatedAnnotation(tokenizer, annotations);

        matchChar(tokenizer, ',');

        PropertyAnnotation annotation1 = parseInstantiatedAnnotation(tokenizer, annotations);

        matchChar(tokenizer, ':');
        matchChar(tokenizer, '=');

        PropertyAnnotation bound = parseInstantiatedAnnotation(tokenizer, annotations);

        String condition;
        next(tokenizer);
        String token = currentToken(tokenizer);
        if (token.equals("for")) {
            condition = matchString(tokenizer);
        } else {
            condition = "true";
            tokenizer.pushBack();
        }

        matchChar(tokenizer, ';');

        return new Bound(
                boundType,
                new UnorderedPair<PropertyAnnotation>(annotation0, annotation1),
                bound,
                condition,
                tokenizer.lineno());

    }

    private PropertyAnnotation parseInstantiatedAnnotation(StreamTokenizer tokenizer, Map<String, PropertyAnnotationType> annotations) throws ParseException {
        String annotationName = matchString(tokenizer);
        if (!annotations.containsKey(annotationName)) {
            throw new ParseException("Unknown annotation @" + annotationName + " in line " + tokenizer.lineno());
        }
        PropertyAnnotationType annotationType = annotations.get(annotationName);
        List<String> actualParameters = new ArrayList<>();
        matchChar(tokenizer, '(');
        for (int i = 0; i < annotationType.getParameters().size(); ++i) {
            if (i != 0) {
                matchChar(tokenizer, ',');
            }
            actualParameters.add(matchString(tokenizer));
        }
        matchChar(tokenizer, ')');

        return new PropertyAnnotation(annotationType, actualParameters);
    }

    private String currentToken(StreamTokenizer tokenizer) throws ParseException {
        switch(tokenizer.ttype) {
        case StreamTokenizer.TT_EOF:
            return null;
        case StreamTokenizer.TT_EOL:
            return "\n";
        case StreamTokenizer.TT_NUMBER:
            return Integer.toString((int) tokenizer.nval);
        case StreamTokenizer.TT_WORD:
        case '\"':
            return tokenizer.sval;
        default:
            return Character.toString((char) tokenizer.ttype);
        }
    }

    private void error(StreamTokenizer tokenizer, String expected) throws ParseException {
        throw new ParseException(
                "Unexpected token \"" + currentToken(tokenizer) + "\" in line " + tokenizer.lineno() +
                "; expected \"" + expected + "\".");
    }

    private String matchString(StreamTokenizer tokenizer) throws ParseException {
        next(tokenizer);
        if (tokenizer.ttype != StreamTokenizer.TT_WORD &&
                tokenizer.ttype != '\"' && tokenizer.ttype != StreamTokenizer.TT_NUMBER) {
            error(tokenizer, "string");
        }

        if (tokenizer.ttype == StreamTokenizer.TT_NUMBER) {
            return Integer.toString((int) tokenizer.nval);
        } else {
            return tokenizer.sval;
        }
    }

    private char matchChar(StreamTokenizer tokenizer, char expected) throws ParseException {
        next(tokenizer);
        char token = (char) tokenizer.ttype;
        if (expected != token) {
            error(tokenizer, Character.toString(expected));
        }
        return token;
    }

    private char matchChar(StreamTokenizer tokenizer, String expected) throws ParseException {
        next(tokenizer);
        char token = (char) tokenizer.ttype;
        if (expected.indexOf(token) < 0) {
            error(tokenizer, "one of: " + expected);
        }
        return token;
    }

    private void next(StreamTokenizer tokenizer) throws ParseException {
        try {
            tokenizer.nextToken();
        } catch (IOException e) {
            throw new ParseException(e);
        }
    }
}
