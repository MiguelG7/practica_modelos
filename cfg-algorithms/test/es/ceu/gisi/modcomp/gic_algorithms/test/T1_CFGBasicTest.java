package es.ceu.gisi.modcomp.gic_algorithms.test;

import es.ceu.gisi.modcomp.gic_algorithms.CFGAlgorithms;
import es.ceu.gisi.modcomp.gic_algorithms.exceptions.CFGAlgorithmsException;
import java.io.FileNotFoundException;
import java.io.IOException;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;



/**
 * Clase que testea el correcto funcionamiento de la implementación del
 * almacenamiento y procesamiento de una gramática independiente del contexto.
 *
 * El objetivo de estos tests es comprobar si la implementación del alumno en la
 * realización de su clase GICAlgorithms cumple con los requisitos básicos
 * respecto a este aspecto.
 *
 * El código del alumno, no obstante, será comprobado con tests adicionales.
 *
 * @author Sergio Saugar García <sergio.saugargarcia@ceu.es>
 */
public class T1_CFGBasicTest {

    private CFGAlgorithms gica;



    public T1_CFGBasicTest() throws IOException, FileNotFoundException, CFGAlgorithmsException {
    }

    @Rule
    public ExpectedException thrown = ExpectedException.none();



    @Test
    public void comprobarAniadirTerminalValido() throws CFGAlgorithmsException {
        gica = new CFGAlgorithms(); 
        gica.addTerminal('a');
    }



    @Test
    public void comprobarAniadirTerminalNoValido1() throws CFGAlgorithmsException {
        thrown.expect(CFGAlgorithmsException.class);
        gica = new CFGAlgorithms();
        gica.addTerminal('0');
    }



    @Test
    public void comprobarAniadirTerminalNoValido2() throws CFGAlgorithmsException {
        thrown.expect(CFGAlgorithmsException.class);
        gica = new CFGAlgorithms();
        gica.addTerminal('A');
    }



    @Test
    public void comprobarAniadirTerminalNoValido3() throws CFGAlgorithmsException {
        thrown.expect(CFGAlgorithmsException.class);
        gica = new CFGAlgorithms();
        gica.addTerminal('a');
        gica.addTerminal('a');
    }



    @Test
    public void comprobarEliminarTerminalValido1() throws CFGAlgorithmsException {
        gica = new CFGAlgorithms();
        gica.addTerminal('a');

        gica.removeTerminal('a');

        assertTrue(gica.getTerminals().isEmpty());
    }



    @Test
    public void comprobarEliminarTerminalValido2() throws CFGAlgorithmsException {
        gica = new CFGAlgorithms();
        gica.addTerminal('a');
        gica.addTerminal('b');
        gica.addNonTerminal('S');
        gica.addNonTerminal('A');
        gica.addProduction('S', "ASa");
        gica.addProduction('S', "b");
        gica.addProduction('S', "l");
        gica.addProduction('A', "l");
        gica.addProduction('A', "a");

        gica.removeTerminal('a');

        assertTrue(gica.getTerminals().size() == 1);
        assertTrue(gica.getTerminals().contains('b'));
        assertEquals("S::=b|l", gica.getProductionsToString('S'));
        assertEquals("A::=l", gica.getProductionsToString('A'));
    }



    @Test
    public void comprobarAniadirNoTerminalValido() throws CFGAlgorithmsException {
        gica = new CFGAlgorithms();
        gica.addNonTerminal('S');
    }



    @Test
    public void comprobarAniadirNoTerminalNoValido1() throws CFGAlgorithmsException {
        thrown.expect(CFGAlgorithmsException.class);
        gica = new CFGAlgorithms();
        gica.addNonTerminal('a');
    }



    @Test
    public void comprobarAniadirNoTerminalNoValido2() throws CFGAlgorithmsException {
        thrown.expect(CFGAlgorithmsException.class);
        gica = new CFGAlgorithms();
        gica.addNonTerminal('0');
    }



    @Test
    public void comprobarAniadirNoTerminalNoValido3() throws CFGAlgorithmsException {
        thrown.expect(CFGAlgorithmsException.class);
        gica = new CFGAlgorithms();
        gica.addNonTerminal('S');
        gica.addNonTerminal('S');
    }



    @Test
    public void comprobarAxiomaNoEstablecido() throws CFGAlgorithmsException {
        thrown.expect(CFGAlgorithmsException.class);
        gica = new CFGAlgorithms();
        gica.addNonTerminal('S');
        gica.getStartSymbol();
    }



    @Test
    public void comprobarEstablecerAxiomaValido() throws CFGAlgorithmsException {
        gica = new CFGAlgorithms();
        gica.addNonTerminal('S');
        gica.setStartSymbol('S');
        assertTrue(gica.getStartSymbol() == 'S');
    }



    @Test
    public void comprobarEstablecerAxiomaNoValido1() throws CFGAlgorithmsException {
        thrown.expect(CFGAlgorithmsException.class);
        gica = new CFGAlgorithms();
        gica.setStartSymbol('S');
    }



    @Test
    public void comprobarEstablecerAxiomaNoValido2() throws CFGAlgorithmsException {
        thrown.expect(CFGAlgorithmsException.class);
        gica = new CFGAlgorithms();
        gica.addNonTerminal('A');
        gica.addTerminal('a');
        gica.setStartSymbol('S');
    }



    @Test
    public void comprobarEstablecerAxiomaNoValido3() throws CFGAlgorithmsException {
        thrown.expect(CFGAlgorithmsException.class);
        gica = new CFGAlgorithms();
        gica.addNonTerminal('A');
        gica.addTerminal('a');
        gica.setStartSymbol('a');
    }



    @Test
    public void comprobarAniadirProduccionValida1() throws CFGAlgorithmsException {
        gica = new CFGAlgorithms();
        gica.addTerminal('a');
        gica.addNonTerminal('S');
        gica.addNonTerminal('A');
        gica.addProduction('S', "ASa");
        gica.addProduction('S', "a");

        assertEquals("S::=ASa|a", gica.getProductionsToString('S'));

    }



    @Test
    public void comprobarAniadirProduccionValida2() throws CFGAlgorithmsException {
        gica = new CFGAlgorithms();
        gica.addTerminal('a');
        gica.addNonTerminal('S');
        gica.addNonTerminal('A');
        gica.addProduction('S', "ASa");
        gica.addProduction('S', "a");
        gica.addProduction('S', "l");
        gica.addProduction('A', "l");

        assertEquals("S::=ASa|a|l", gica.getProductionsToString('S'));
        assertEquals("A::=l", gica.getProductionsToString('A'));
    }



    @Test
    public void comprobarAniadirProduccionNoValida1() throws CFGAlgorithmsException {
        thrown.expect(CFGAlgorithmsException.class);
        gica = new CFGAlgorithms();
        gica.addTerminal('a');

        gica.addNonTerminal('S');
        gica.addNonTerminal('A');

        gica.addProduction('S', "b");
    }



    @Test
    public void comprobarAniadirProduccionNoValida2() throws CFGAlgorithmsException {
        thrown.expect(CFGAlgorithmsException.class);
        gica = new CFGAlgorithms();
        gica.addTerminal('a');

        gica.addNonTerminal('S');
        gica.addNonTerminal('A');

        gica.addProduction('C', "a");
    }



    @Test
    public void comprobarAniadirProduccionNoValida3() throws CFGAlgorithmsException {
        thrown.expect(CFGAlgorithmsException.class);
        gica = new CFGAlgorithms();
        gica.addTerminal('a');

        gica.addNonTerminal('S');
        gica.addNonTerminal('A');
        gica.addProduction('S', "AB");
    }



    @Test
    public void comprobarAniadirProduccionNoValida4() throws CFGAlgorithmsException {
        thrown.expect(CFGAlgorithmsException.class);
        gica = new CFGAlgorithms();
        gica.addTerminal('a');

        gica.addNonTerminal('S');
        gica.addNonTerminal('B');

        gica.addProduction('S', "Aa");
    }



    @Test
    public void comprobarAniadirProduccionNoValida5() throws CFGAlgorithmsException {
        thrown.expect(CFGAlgorithmsException.class);
        gica = new CFGAlgorithms();
        gica.addTerminal('a');

        gica.addNonTerminal('S');
        gica.addNonTerminal('A');
        gica.addProduction('A', "aABS");
    }



    @Test
    public void comprobarAniadirProduccionNoValida6() throws CFGAlgorithmsException {
        thrown.expect(CFGAlgorithmsException.class);
        gica = new CFGAlgorithms();
        gica.addTerminal('a');

        gica.addNonTerminal('S');
        gica.addNonTerminal('A');

        gica.addProduction('A', "aSbB");
    }



    @Test
    public void comprobarAniadirProduccionNoValida7() throws CFGAlgorithmsException {
        thrown.expect(CFGAlgorithmsException.class);
        gica = new CFGAlgorithms();
        gica.addTerminal('a');

        gica.addNonTerminal('S');
        gica.addNonTerminal('A');

        gica.addProduction('A', "SAAb");
    }



    @Test
    public void comprobarAniadirProduccionNoValida8() throws CFGAlgorithmsException {
        thrown.expect(CFGAlgorithmsException.class);
        gica = new CFGAlgorithms();
        gica.addTerminal('a');

        gica.addNonTerminal('S');
        gica.addNonTerminal('A');

        gica.addProduction('A', "SA");
        gica.addProduction('A', "SA");
    }



    @Test
    public void comprobarEliminaProduccionValida1() throws CFGAlgorithmsException {
        gica = new CFGAlgorithms();
        gica.addTerminal('a');
        gica.addNonTerminal('S');
        gica.addNonTerminal('A');
        gica.addProduction('S', "ASa");
        gica.addProduction('S', "a");

        gica.removeProduction('S', "ASa");
        assertEquals("S::=a", gica.getProductionsToString('S'));

    }



    @Test
    public void comprobarEliminaProduccionValida2() throws CFGAlgorithmsException {
        gica = new CFGAlgorithms();
        gica.addTerminal('a');
        gica.addNonTerminal('S');
        gica.addNonTerminal('A');
        gica.addProduction('S', "ASa");
        gica.addProduction('S', "a");

        gica.removeProduction('S', "a");
        assertEquals("S::=ASa", gica.getProductionsToString('S'));
    }



    @Test
    public void comprobarEliminaProduccionNoValida1() throws CFGAlgorithmsException {
        thrown.expect(CFGAlgorithmsException.class);
        gica = new CFGAlgorithms();
        gica.addTerminal('a');
        gica.addNonTerminal('S');
        gica.addNonTerminal('A');
        gica.addProduction('S', "ASa");
        gica.addProduction('S', "a");

        gica.removeProduction('S', "b");
    }



    @Test
    public void comprobarRecuperarProducciones() throws CFGAlgorithmsException {
        gica = new CFGAlgorithms();
        gica.addNonTerminal('S');
        gica.addNonTerminal('A');
        gica.addNonTerminal('B');
        gica.addNonTerminal('C');

        gica.addTerminal('a');
        gica.addTerminal('b');

        gica.setStartSymbol('S');

        gica.addProduction('S', "AB");
        gica.addProduction('S', "BC");

        gica.addProduction('A', "BA");
        gica.addProduction('A', "a");

        gica.addProduction('B', "CC");
        gica.addProduction('B', "b");

        gica.addProduction('C', "AB");
        gica.addProduction('C', "a");

        assertEquals("S::=AB|BC", gica.getProductionsToString('S'));
        assertEquals("A::=BA|a", gica.getProductionsToString('A'));
        assertEquals("B::=CC|b", gica.getProductionsToString('B'));
        assertEquals("C::=AB|a", gica.getProductionsToString('C'));

    }



    @Test
    public void comprobarEliminarGramaticaValido() throws CFGAlgorithmsException {
        gica = new CFGAlgorithms();
        gica.addNonTerminal('S');
        gica.addNonTerminal('A');
        gica.addNonTerminal('B');
        gica.addNonTerminal('C');

        gica.addTerminal('a');
        gica.addTerminal('b');

        gica.setStartSymbol('S');

        gica.addProduction('S', "AB");
        gica.addProduction('S', "BC");

        gica.addProduction('A', "BA");
        gica.addProduction('A', "a");

        gica.addProduction('B', "CC");
        gica.addProduction('B', "b");

        gica.addProduction('C', "AB");
        gica.addProduction('C', "a");

        gica.deleteGrammar();

        assertEquals("", gica.getProductionsToString('S'));
        assertEquals("", gica.getProductionsToString('A'));
        assertEquals("", gica.getProductionsToString('B'));
        assertEquals("", gica.getProductionsToString('C'));

        gica.addNonTerminal('S');
        gica.addNonTerminal('A');
        gica.addNonTerminal('B');
        gica.addNonTerminal('C');

        gica.addTerminal('a');
        gica.addTerminal('b');
    }



    @Test
    public void comprobarEsGICValido1() throws CFGAlgorithmsException {
        gica = new CFGAlgorithms();
        gica.addNonTerminal('S');
        gica.addNonTerminal('A');
        gica.addNonTerminal('B');
        gica.addNonTerminal('C');
        gica.addNonTerminal('D');

        gica.addTerminal('a');
        gica.addTerminal('b');
        gica.addTerminal('c');

        gica.setStartSymbol('S');

        gica.addProduction('S', "aAbB");
        gica.addProduction('S', "C");

        gica.addProduction('A', "A");
        gica.addProduction('A', "abab");

        gica.addProduction('B', "CC");
        gica.addProduction('B', "l");

        gica.addProduction('C', "Baaa");
        gica.addProduction('C', "CaD");

        assertTrue(gica.isCFG());
    }
}
