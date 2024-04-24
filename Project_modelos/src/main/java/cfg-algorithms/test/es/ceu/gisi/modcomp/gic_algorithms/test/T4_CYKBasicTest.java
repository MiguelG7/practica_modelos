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
 * Clase que testea el correcto funcionamiento de la implementación del
 * algoritmo CYK haciendo uso de la clase CYKAlgorithm.
 *
 * El objetivo de estos tests es comprobar si la implementación del alumno en la
 * realización de su clase GICAlgorithms cumple con los requisitos básicos
 * respecto a este aspecto.
 *
 * El código del alumno, no obstante, será comprobado con tests adicionales.
 *
 * @author Sergio Saugar García <sergio.saugargarcia@ceu.es>
 */
public class T4_CYKBasicTest {

    private CFGAlgorithms gica;



    public T4_CYKBasicTest() throws IOException, FileNotFoundException, CFGAlgorithmsException {
    }

    @Rule
    public ExpectedException thrown = ExpectedException.none();



    @Test
    public void comprobarDerivacionNoValido1() throws CFGAlgorithmsException {
        thrown.expect(CFGAlgorithmsException.class);

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

        gica.isDerivedUsignCYK("bbBbb");
    }



    @Test
    public void comprobarDerivacionNoValido2() throws CFGAlgorithmsException {
        thrown.expect(CFGAlgorithmsException.class);

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

        gica.isDerivedUsignCYK("caabb");
    }



    @Test
    public void comprobarDerivacionValido1() throws CFGAlgorithmsException {

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

        assertTrue(gica.isDerivedUsignCYK("baaba"));
    }



    @Test
    public void comprobarDerivacionValido2() throws CFGAlgorithmsException {

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

        assertFalse(gica.isDerivedUsignCYK("bbb"));
    }
}
