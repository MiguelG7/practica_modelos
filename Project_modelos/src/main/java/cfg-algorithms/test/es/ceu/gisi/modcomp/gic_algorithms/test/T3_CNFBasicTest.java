package es.ceu.gisi.modcomp.gic_algorithms.test;

import es.ceu.gisi.modcomp.gic_algorithms.CFGAlgorithms;
import es.ceu.gisi.modcomp.gic_algorithms.exceptions.CFGAlgorithmsException;
import java.io.FileNotFoundException;
import java.io.IOException;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;



/**
 * Clase que testea el correcto funcionamiento de la implementación del cálculo
 * de una Forma Normal de Chomsky a partir de una gramática independiente del
 * contexto.
 *
 * El objetivo de estos tests es comprobar si la implementación del alumno en la
 * realización de su clase GICAlgorithms cumple con los requisitos básicos
 * respecto a este aspecto.
 *
 * El código del alumno, no obstante, será comprobado con tests adicionales.
 *
 * @author Sergio Saugar García <sergio.saugargarcia@ceu.es>
 */
public class T3_CNFBasicTest {

    private CFGAlgorithms gica;



    public T3_CNFBasicTest() throws IOException, FileNotFoundException, CFGAlgorithmsException {
    }

    @Rule
    public ExpectedException thrown = ExpectedException.none();



    @Test
    public void comprobarCheckCNFProductionCorrecto() throws CFGAlgorithmsException {
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

        gica.checkCNFProduction('S', "l");
        gica.checkCNFProduction('S', "AB");
        gica.checkCNFProduction('S', "b");
        gica.checkCNFProduction('D', "BB");
    }



    @Test
    public void comprobarCheckCNFProductionNoValido1() throws CFGAlgorithmsException {
        thrown.expect(CFGAlgorithmsException.class);
        gica = new CFGAlgorithms();
        gica.addTerminal('a');

        gica.addNonTerminal('S');

        gica.setStartSymbol('S');

        gica.checkCNFProduction('A', "l");
    }



    @Test
    public void comprobarCheckCNFProductionNoValido2() throws CFGAlgorithmsException {
        thrown.expect(CFGAlgorithmsException.class);
        gica = new CFGAlgorithms();
        gica.addTerminal('a');
        gica.addNonTerminal('S');
        gica.addNonTerminal('A');

        gica.setStartSymbol('S');

        gica.checkCNFProduction('A', "l");
    }



    @Test
    public void comprobarCheckCNFProductionNoValido3() throws CFGAlgorithmsException {
        thrown.expect(CFGAlgorithmsException.class);
        gica = new CFGAlgorithms();
        gica.addTerminal('a');

        gica.addNonTerminal('S');
        gica.addNonTerminal('A');
        gica.addNonTerminal('B');

        gica.setStartSymbol('S');

        gica.checkCNFProduction('A', "ABS");
    }



    @Test
    public void comprobarCheckCNFProductionNoValido4() throws CFGAlgorithmsException {
        thrown.expect(CFGAlgorithmsException.class);
        gica = new CFGAlgorithms();
        gica.addTerminal('a');

        gica.addNonTerminal('S');
        gica.addNonTerminal('A');

        gica.setStartSymbol('S');

        gica.checkCNFProduction('A', "aa");
    }



    @Test
    public void comprobarCheckCNFProductionNoValido5() throws CFGAlgorithmsException {
        thrown.expect(CFGAlgorithmsException.class);
        gica = new CFGAlgorithms();
        gica.addTerminal('a');

        gica.addNonTerminal('S');
        gica.addNonTerminal('A');

        gica.setStartSymbol('S');

        gica.checkCNFProduction('A', "aA");
    }



    @Test
    public void comprobarIsCNFCorrecto() throws CFGAlgorithmsException {
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

        gica.addProduction('S', "l");
        gica.addProduction('S', "AB");
        gica.addProduction('S', "b");
        gica.addProduction('A', "d");
        gica.addProduction('B', "DC");
        gica.addProduction('B', "a");
        gica.addProduction('C', "a");
        gica.addProduction('D', "BB");

        assertTrue(gica.isCNF());
    }



    @Test
    public void comprobarIsCNFNoValido1() throws CFGAlgorithmsException {
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

        gica.addProduction('S', "l");
        gica.addProduction('S', "AB");
        gica.addProduction('S', "b");
        gica.addProduction('A', "d");
        gica.addProduction('B', "DC");
        gica.addProduction('B', "a");
        gica.addProduction('C', "a");
        gica.addProduction('D', "l");

        assertFalse(gica.isCNF());
    }



    @Test
    public void comprobarIsCNFNoValido2() throws CFGAlgorithmsException {
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

        gica.addProduction('S', "l");
        gica.addProduction('S', "AB");
        gica.addProduction('S', "b");
        gica.addProduction('A', "d");
        gica.addProduction('B', "DC");
        gica.addProduction('B', "aD");
        gica.addProduction('C', "a");
        gica.addProduction('D', "d");

        assertFalse(gica.isCNF());
    }



    @Test
    public void comprobarTransformIntoCNFValido1() throws CFGAlgorithmsException {
        gica = new CFGAlgorithms();
        gica.addTerminal('a');
        gica.addTerminal('b');

        gica.addNonTerminal('S');

        gica.setStartSymbol('S');

        gica.addProduction('S', "l");
        gica.addProduction('S', "aSb");

        gica.transformToWellFormedGrammar();

        gica.transformIntoCNF();

        assertTrue(gica.isCNF());
        assertTrue(gica.getNonTerminals().size() == 4);
        assertTrue(gica.getProductions(gica.getStartSymbol()).size() == 3);

    }



    @Test
    public void comprobarTransformIntoCNFValido2() throws CFGAlgorithmsException {
        gica = new CFGAlgorithms();
        gica.addTerminal('a');
        gica.addTerminal('b');
        gica.addTerminal('c');

        gica.addNonTerminal('S');
        gica.addNonTerminal('A');
        gica.addNonTerminal('B');

        gica.setStartSymbol('S');

        gica.addProduction('S', "Aba");
        gica.addProduction('S', "a");
        gica.addProduction('S', "BbA");
        gica.addProduction('S', "l");

        gica.addProduction('A', "aab");
        gica.addProduction('A', "Acbc");

        gica.addProduction('B', "Ac");

        gica.transformToWellFormedGrammar();

        gica.transformIntoCNF();

        assertTrue(gica.isCNF());
        assertTrue(gica.getNonTerminals().size() == 11);
        assertTrue(gica.getProductions(gica.getStartSymbol()).size() == 4);
    }

}
