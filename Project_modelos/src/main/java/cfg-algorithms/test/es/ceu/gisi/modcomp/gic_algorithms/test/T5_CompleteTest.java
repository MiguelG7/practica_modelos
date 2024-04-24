package es.ceu.gisi.modcomp.gic_algorithms.test;

import es.ceu.gisi.modcomp.gic_algorithms.CFGAlgorithms;
import es.ceu.gisi.modcomp.gic_algorithms.exceptions.CFGAlgorithmsException;
import java.io.FileNotFoundException;
import java.io.IOException;
import static org.junit.Assert.assertTrue;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;



/**
 * Clase que testea el correcto funcionamiento de la completa de la práctica.
 *
 * El objetivo de estos tests es comprobar si la implementación de los
 * algoritmos del alumno en la realización de su clase GICAlgorithms cumple con
 * los requisitos básicos respecto a este aspecto.
 *
 * El código del alumno, no obstante, será comprobado con tests adicionales.
 *
 * @author Sergio Saugar García <sergio.saugargarcia@ceu.es>
 */
public class T5_CompleteTest {

    private CFGAlgorithms gica;



    public T5_CompleteTest() throws IOException, FileNotFoundException, CFGAlgorithmsException {
    }

    @Rule
    public ExpectedException thrown = ExpectedException.none();



    @Test
    public void completeTestValido1() throws CFGAlgorithmsException {
        gica = new CFGAlgorithms();
        gica.addTerminal('a');
        gica.addTerminal('b');
        gica.addTerminal('c');

        gica.addNonTerminal('S');
        gica.addNonTerminal('A');
        gica.addNonTerminal('B');
        gica.addNonTerminal('C');
        gica.addNonTerminal('D');
        gica.addNonTerminal('E');
        gica.addNonTerminal('F');
        gica.addNonTerminal('G');

        gica.setStartSymbol('S');

        gica.addProduction('S', "AB");
        gica.addProduction('S', "ASA");
        //gica.addProduction('S', "EbDaFbE");

        gica.addProduction('A', "BS");
        gica.addProduction('A', "ASAS");
        gica.addProduction('A', "b");
        gica.addProduction('A', "bE");

        gica.addProduction('B', "SA");
        gica.addProduction('B', "SASAS");
        gica.addProduction('B', "a");
        gica.addProduction('B', "ab");

        gica.addProduction('C', "ab");

        gica.addProduction('D', "b");

        gica.addProduction('E', "F");

        gica.addProduction('F', "l");

        gica.transformToWellFormedGrammar();

        System.out.println("WFG: \n" + gica.getGrammar());

        gica.transformIntoCNF();
        System.out.println("CNF: \n" + gica.getGrammar());

        assertTrue(gica.isDerivedUsignCYK("bbabb"));
        System.out.println(gica.algorithmCYKStateToString("bbabb"));

        assertTrue(gica.isDerivedUsignCYK("bbab"));
        System.out.println(gica.algorithmCYKStateToString("bbab"));
    }
}
