package es.ceu.gisi.modcomp.gic_algorithms.test;

import es.ceu.gisi.modcomp.gic_algorithms.CFGAlgorithms;
import es.ceu.gisi.modcomp.gic_algorithms.exceptions.CFGAlgorithmsException;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.List;
import static org.junit.Assert.*;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;



/**
 * Clase que testea el correcto funcionamiento de la implementación de los
 * algoritmos de limpieza de gramáticas y la obtención de una gramática bien
 * formada
 *
 * El objetivo de estos tests es comprobar si la implementación del alumno en la
 * realización de su clase GICAlgorithms cumple con los requisitos básicos
 * respecto a este aspecto.
 *
 * El código del alumno, no obstante, será comprobado con tests adicionales.
 *
 * @author Sergio Saugar García <sergio.saugargarcia@ceu.es>
 */
public class T2_WFCFGBasicTest {

    private CFGAlgorithms gica;



    public T2_WFCFGBasicTest() throws IOException, FileNotFoundException, CFGAlgorithmsException {
    }

    @Rule
    public ExpectedException thrown = ExpectedException.none();



    @Test
    public void comprobarTieneReglasInnecesarias1() throws CFGAlgorithmsException {
        gica = new CFGAlgorithms();
        gica.addTerminal('a');
        gica.addNonTerminal('S');
        gica.addProduction('S', "Sa");
        gica.addProduction('S', "S");
        gica.addProduction('S', "a");

        assertTrue(gica.hasUselessProductions());
    }



    @Test
    public void comprobarTieneReglasInnecesarias2() throws CFGAlgorithmsException {
        gica = new CFGAlgorithms();
        gica.addTerminal('a');
        gica.addNonTerminal('S');
        gica.addProduction('S', "Sa");
        gica.addProduction('S', "a");

        assertFalse(gica.hasUselessProductions());
    }



    @Test
    public void comprobarTieneReglasInnecesarias3() throws CFGAlgorithmsException {
        gica = new CFGAlgorithms();
        gica.addTerminal('a');
        gica.addNonTerminal('S');
        gica.addNonTerminal('A');
        gica.addProduction('S', "Sa");
        gica.addProduction('S', "A");
        gica.addProduction('S', "a");

        assertFalse(gica.hasUselessProductions());
    }



    @Test
    public void comprobarEliminarReglasInnecesarias() throws CFGAlgorithmsException {
        gica = new CFGAlgorithms();
        gica.addTerminal('a');
        gica.addNonTerminal('S');
        gica.addNonTerminal('B');
        gica.addProduction('S', "Sa");
        gica.addProduction('S', "S");
        gica.addProduction('S', "B");
        gica.addProduction('S', "a");

        assertTrue(gica.hasUselessProductions());
        List<String> lista = gica.removeUselessProductions();
        assertEquals(1, lista.size());
        assertEquals("S::=S", lista.get(0));
        assertEquals("S::=B|Sa|a", gica.getProductionsToString('S'));
        assertFalse(gica.hasUselessProductions());

    }



    @Test
    public void eliminarSimbolosInnecesarios1() throws CFGAlgorithmsException {
        gica = new CFGAlgorithms();
        gica.addTerminal('a');
        gica.addNonTerminal('S');
        gica.addNonTerminal('A');
        gica.addNonTerminal('B');

        gica.setStartSymbol('S');

        gica.addProduction('S', "AB");
        gica.addProduction('S', "a");
        gica.addProduction('A', "a");

        gica.removeUselessSymbols();

        assertTrue(gica.getNonTerminals().size() == 1);
        assertTrue(gica.getTerminals().size() == 1);
        assertEquals("S::=a", gica.getProductionsToString('S'));
    }



    @Test
    public void eliminarSimbolosInnecesarios2() throws CFGAlgorithmsException {
        gica = new CFGAlgorithms();
        gica.addTerminal('a');
        gica.addTerminal('b');
        gica.addTerminal('c');
        gica.addTerminal('d');

        gica.addNonTerminal('S');
        gica.addNonTerminal('A');
        gica.addNonTerminal('B');
        gica.addNonTerminal('C');
        gica.addNonTerminal('D');
        gica.addNonTerminal('E');

        gica.setStartSymbol('S');

        gica.addProduction('S', "Aa");
        gica.addProduction('S', "B");
        gica.addProduction('S', "D");

        gica.addProduction('B', "b");

        gica.addProduction('A', "Aa");
        gica.addProduction('A', "bA");
        gica.addProduction('A', "B");
        gica.addProduction('A', "cE");

        gica.addProduction('E', "l");

        gica.addProduction('D', "Db");

        gica.removeUselessSymbols();

        assertTrue(gica.getNonTerminals().size() == 4);
        assertTrue(gica.getTerminals().size() == 3);

        assertEquals("S::=Aa|B", gica.getProductionsToString('S'));
        assertEquals("B::=b", gica.getProductionsToString('B'));
        assertEquals("A::=Aa|B|bA|cE", gica.getProductionsToString('A'));
        assertEquals("E::=l", gica.getProductionsToString('E'));
    }



    @Test
    public void contieneProduccionesLambda1() throws CFGAlgorithmsException {
        gica = new CFGAlgorithms();
        gica.addTerminal('a');

        gica.addNonTerminal('S');
        gica.addNonTerminal('A');

        gica.setStartSymbol('S');

        gica.addProduction('S', "Aa");
        gica.addProduction('S', "l");

        gica.addProduction('A', "Aa");
        gica.addProduction('A', "a");

        assertTrue(gica.hasLambdaProductions());
    }



    @Test
    public void contieneProduccionesLambda2() throws CFGAlgorithmsException {
        gica = new CFGAlgorithms();
        gica.addTerminal('a');
        gica.addTerminal('b');
        gica.addTerminal('c');
        gica.addTerminal('d');

        gica.addNonTerminal('S');
        gica.addNonTerminal('A');
        gica.addNonTerminal('B');
        gica.addNonTerminal('C');
        gica.addNonTerminal('D');
        gica.addNonTerminal('E');

        gica.setStartSymbol('S');

        gica.addProduction('S', "Aa");
        gica.addProduction('S', "B");
        gica.addProduction('S', "D");

        gica.addProduction('B', "b");

        gica.addProduction('A', "Aa");
        gica.addProduction('A', "bA");
        gica.addProduction('A', "B");
        gica.addProduction('A', "cE");

        gica.addProduction('E', "l");

        gica.addProduction('D', "Db");

        assertTrue(gica.hasLambdaProductions());
    }



    @Test
    public void noContieneProduccionesLambda1() throws CFGAlgorithmsException {
        gica = new CFGAlgorithms();
        gica.addTerminal('a');

        gica.addNonTerminal('S');
        gica.addNonTerminal('A');

        gica.setStartSymbol('S');

        gica.addProduction('S', "Aa");

        gica.addProduction('A', "Aa");
        gica.addProduction('A', "a");

        assertFalse(gica.hasLambdaProductions());
    }



    @Test
    public void eliminaProduccionesLambda1() throws CFGAlgorithmsException {
        gica = new CFGAlgorithms();
        gica.addTerminal('a');
        gica.addTerminal('b');
        gica.addTerminal('c');
        gica.addTerminal('d');

        gica.addNonTerminal('S');
        gica.addNonTerminal('A');
        gica.addNonTerminal('B');
        gica.addNonTerminal('C');
        gica.addNonTerminal('D');

        gica.setStartSymbol('S');

        gica.addProduction('S', "Aa");
        gica.addProduction('S', "B");
        gica.addProduction('S', "C");

        gica.addProduction('B', "b");

        gica.addProduction('A', "Aa");
        gica.addProduction('A', "bA");
        gica.addProduction('A', "B");
        gica.addProduction('A', "cD");

        gica.addProduction('D', "l");

        gica.addProduction('C', "Cb");

        assertTrue(gica.hasLambdaProductions());

        gica.removeLambdaProductions();

        assertEquals("S::=Aa|B|C", gica.getProductionsToString('S'));
        assertEquals("A::=Aa|B|bA|c|cD", gica.getProductionsToString('A'));
        assertEquals("C::=Cb", gica.getProductionsToString('C'));
        assertEquals("B::=b", gica.getProductionsToString('B'));
        assertTrue(gica.getProductions('D') == null || gica.getProductions('D').isEmpty());
    }



    @Test
    public void eliminaProduccionesLambda2() throws CFGAlgorithmsException {
        gica = new CFGAlgorithms();
        gica.addTerminal('a');
        gica.addTerminal('b');

        gica.addNonTerminal('S');

        gica.setStartSymbol('S');

        gica.addProduction('S', "aSb");
        gica.addProduction('S', "l");

        assertTrue(gica.hasLambdaProductions());

        gica.removeLambdaProductions();

        assertEquals("S::=aSb|ab|l", gica.getProductionsToString('S'));
    }



    @Test
    public void eliminaProduccionesLambda3() throws CFGAlgorithmsException {
        gica = new CFGAlgorithms();
        gica.addTerminal('a');
        gica.addTerminal('b');
        gica.addTerminal('c');

        gica.addNonTerminal('S');
        gica.addNonTerminal('A');
        gica.addNonTerminal('B');
        gica.addNonTerminal('E');

        gica.setStartSymbol('S');

        gica.addProduction('S', "Aa");
        gica.addProduction('S', "B");
        gica.addProduction('B', "bB");
        gica.addProduction('B', "b");
        gica.addProduction('B', "l");
        gica.addProduction('A', "Aa");
        gica.addProduction('A', "bA");
        gica.addProduction('A', "BEE");
        gica.addProduction('E', "l");

        assertTrue(gica.hasLambdaProductions());

        gica.removeLambdaProductions();

        assertEquals("S::=Aa|B|a|l", gica.getProductionsToString('S'));
        assertEquals("B::=b|bB", gica.getProductionsToString('B'));
        assertEquals("A::=Aa|B|BE|BEE|E|EE|a|b|bA", gica.getProductionsToString('A'));
    }



    @Test
    public void comprobarTieneReglasUnitarias1() throws CFGAlgorithmsException {
        gica = new CFGAlgorithms();
        gica.addTerminal('a');
        gica.addNonTerminal('S');
        gica.addNonTerminal('A');

        gica.setStartSymbol('S');

        gica.addProduction('S', "Sa");
        gica.addProduction('S', "A");
        gica.addProduction('S', "a");

        assertTrue(gica.hasUnitProductions());
    }



    @Test
    public void eliminarReglasUnitarias1() throws CFGAlgorithmsException {
        gica = new CFGAlgorithms();
        gica.addTerminal('a');
        gica.addTerminal('b');
        gica.addTerminal('c');

        gica.addNonTerminal('S');
        gica.addNonTerminal('A');
        gica.addNonTerminal('B');
        gica.addNonTerminal('C');
        gica.addNonTerminal('E');

        gica.setStartSymbol('S');

        gica.addProduction('S', "Aa");
        gica.addProduction('S', "a");
        gica.addProduction('S', "C");
        gica.addProduction('S', "BE");
        gica.addProduction('S', "B");
        gica.addProduction('S', "l");
        gica.addProduction('A', "Aa");
        gica.addProduction('A', "a");
        gica.addProduction('C', "B");
        gica.addProduction('B', "bB");
        gica.addProduction('B', "b");
        gica.addProduction('B', "S");
        gica.addProduction('E', "c");

        assertTrue(gica.hasUnitProductions());

        gica.removeUnitProductions();

        assertEquals("S::=Aa|BE|a|b|bB|c|l", gica.getProductionsToString('S'));
        assertEquals("A::=Aa|a", gica.getProductionsToString('A'));
        assertEquals("B::=Aa|BE|a|b|bB|c", gica.getProductionsToString('B'));
        assertEquals("C::=Aa|BE|a|b|bB|c", gica.getProductionsToString('C'));
        assertEquals("E::=c", gica.getProductionsToString('E'));
    }



    @Test
    public void comprobarGramáticaBienFormada1() throws CFGAlgorithmsException {
        gica = new CFGAlgorithms();
        gica.addTerminal('a');
        gica.addTerminal('b');

        gica.addNonTerminal('S');
        gica.addNonTerminal('A');
        gica.addNonTerminal('B');

        gica.addNonTerminal('D');
        gica.addNonTerminal('E');
        gica.addNonTerminal('F');

        gica.setStartSymbol('S');

        gica.addProduction('S', "AB");
        gica.addProduction('S', "A");
        gica.addProduction('S', "aE");

        gica.addProduction('A', "aAS");
        gica.addProduction('A', "l");
        gica.addProduction('A', "Aa");

        gica.addProduction('B', "Bb");
        gica.addProduction('B', "b");

        gica.addProduction('D', "Bb");
        gica.addProduction('D', "l");
        gica.addProduction('D', "bF");

        gica.addProduction('E', "Eb");

        gica.addProduction('F', "aD");

        gica.transformToWellFormedGrammar();

        assertEquals("A::=Aa|a|aA|aAS|aS", gica.getProductionsToString('A'));
        assertEquals("B::=Bb|b", gica.getProductionsToString('B'));
        assertEquals("S::=AB|Aa|Bb|a|aA|aAS|aS|b|l", gica.getProductionsToString('S'));
    }



    @Test
    public void comprobarGramáticaBienFormada2() throws CFGAlgorithmsException {
        gica = new CFGAlgorithms();
        gica.addTerminal('a');
        gica.addTerminal('b');
        gica.addTerminal('d');

        gica.addNonTerminal('S');
        gica.addNonTerminal('A');
        gica.addNonTerminal('B');
        gica.addNonTerminal('C');
        gica.addNonTerminal('D');

        gica.setStartSymbol('S');

        gica.addProduction('S', "AbaC");
        gica.addProduction('A', "BC");
        gica.addProduction('B', "b");
        gica.addProduction('B', "l");
        gica.addProduction('C', "D");
        gica.addProduction('C', "l");
        gica.addProduction('D', "d");

        gica.transformToWellFormedGrammar();

        assertEquals("S::=Aba|AbaC|ba|baC", gica.getProductionsToString('S'));
        assertEquals("A::=BC|b|d", gica.getProductionsToString('A'));
        assertEquals("B::=b", gica.getProductionsToString('B'));
        assertEquals("C::=d", gica.getProductionsToString('C'));
    }

}
