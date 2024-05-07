package es.ceu.gisi.modcomp.gic_algorithms.interfaces;

import es.ceu.gisi.modcomp.gic_algorithms.exceptions.CFGAlgorithmsException;



/**
 * Interfaz que proporciona todos los métodos que deben implementar los alumnos
 * para dar soporte a la gestión de una gramática independiente del contexto en
 * FORMA NORMAL de CHOMSKY.
 *
 * @author Sergio Saugar <sergio.saugargarcia@ceu.es>
 */
public interface CNFInterface {

    /**
     * Método que chequea que las producciones estén en Forma Normal de Chomsky.
     *
     * @param nonterminal A
     * @param production  A::=BC o A::=a (siendo B, C no terminales definidos
     *                    previamente y a terminal definido previamente). Se acepta S::=l si S es
     *                    no terminal y axioma.
     *
     * @throws CFGAlgorithmsException Si no se ajusta a Forma Normal de Chomsky
     *                                o si está compuesta por elementos
     *                                (terminales o no terminales) no definidos
     *                                previamente.
     */
    public void checkCNFProduction(char nonterminal, String production) throws CFGAlgorithmsException;



    /**
     * Método que comprueba si la gramática dada de alta se encuentra en Forma
     * Normal de Chomsky. Es una precondición para la aplicación del algoritmo
     * CYK.
     *
     * @return true Si la gramática está en Forma Normal de Chomsky
     */
    public boolean isCNF();



    /**
     * Método que transforma la gramática almacenada en su Forma Normal de
     * Chomsky equivalente.
     *
     * @throws CFGAlgorithmsException Si la gramática de la que partimos no es
     *                                una gramática bien formada.
     */
    public void transformIntoCNF() throws CFGAlgorithmsException;
}
