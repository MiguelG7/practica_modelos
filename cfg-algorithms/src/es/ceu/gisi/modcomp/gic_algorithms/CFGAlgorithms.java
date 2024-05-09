package es.ceu.gisi.modcomp.gic_algorithms;

import es.ceu.gisi.modcomp.gic_algorithms.exceptions.CFGAlgorithmsException;
import es.ceu.gisi.modcomp.gic_algorithms.interfaces.*;
import java.util.List;
import java.util.Set;
import java.util.HashSet;
import java.util.HashMap;
import java.util.Map;
import java.util.Collections;

import java.util.ArrayList;



/**
 * Esta clase contiene la implementación de las interfaces que establecen los
 * métodos necesarios para el correcto funcionamiento del
 * proyecto de programación de la asignatura Modelos de Computación.
 *
 * @author Sergio Saugar García <sergio.saugargarcia@ceu.es>
 */
public class CFGAlgorithms implements CFGInterface, WFCFGInterface, CNFInterface, CYKInterface {
    
    private Set<Character> noTerminales = new HashSet<>();
    private Set<Character> terminales = new HashSet<>();
    private Map<Character, Set<String>> producciones = new HashMap<>();
    private Character simboloInicio;

    /**
     * Método que añade los elementos no terminales de la gramática.
     *
     * @param nonterminal Por ejemplo, 'S'
     *
     * @throws CFGAlgorithmsException Si el elemento no es una letra mayúscula o
     *                                si ya está en el conjunto.
     */
    public void addNonTerminal(char nonterminal) throws CFGAlgorithmsException {
        // Compruebo que sea letra mayúscula
        if (!Character.isUpperCase(nonterminal)) {
            throw new CFGAlgorithmsException("Compruebo que sea mayúscula");
        }

        // Compruebo si está repetida
        if (noTerminales.contains(nonterminal)) {
            throw new CFGAlgorithmsException("UEPAAA! El elemento ya está en el conjunto.");
        }

        // Añado al conjunto de noTerminales
        noTerminales.add(nonterminal);
        
        
    }



    /**
     * Método que elimina el símbolo no terminal indicado de la gramática.
     * También debe eliminar todas las producciones asociadas a él y las
     * producciones en las que aparece.
     *
     * @param nonterminal Elemento no terminal a eliminar.
     *
     * @throws CFGAlgorithmsException Si el elemento no pertenece a la gramática
     */
    public void removeNonTerminal(char nonterminal) throws CFGAlgorithmsException {
        // Caracter en conjunto????
        if (!noTerminales.contains(nonterminal)) {
            throw new CFGAlgorithmsException("El elemento no pertenece a la gramática.");
        }

        noTerminales.remove(nonterminal);

        //eliminamos producciones q tengan el terminal
        for (Set<String> prods : producciones.values()) {
            prods.removeIf(produccion -> produccion.indexOf(nonterminal) != -1);
        }
    }



    /**
     * Método que devuelve un conjunto con todos los símbolos no terminales de
     * la gramática.
     *
     * @return Un conjunto con los no terminales definidos.
     */
    public Set<Character> getNonTerminals() {
        return new HashSet<>(noTerminales);
    }



    /**
     * Método que añade los elementos terminales de la gramática.
     *
     * @param terminal Por ejemplo, 'a'
     *
     * @throws CFGAlgorithmsException Si el elemento no es una letra minúscula o
     *                                si ya está en el conjunto.
     */
    public void addTerminal(char terminal) throws CFGAlgorithmsException {
        
        // Compruebo que sea letra minúscula
        if (!Character.isLowerCase(terminal)) {
            throw new CFGAlgorithmsException("UEPAAA! letra minúscula.");
        }

        // Compruebo si está repetida
        if (terminales.contains(terminal)) {
            throw new CFGAlgorithmsException("UEPAAA! El elemento ya está en el conjunto");
        }
        terminales.add(terminal);
    }



    /**
     * Método que elimina el símbolo terminal indicado de la gramática.
     * También debe eliminar todas las producciones en las que aparece.
     *
     * @param terminal Elemento terminal a eliminar.
     *
     * @throws CFGAlgorithmsException Si el elemento no pertenece a la gramática
     */
    public void removeTerminal(char terminal) throws CFGAlgorithmsException {
        // Caracter en conjunto????
        if (!terminales.contains(terminal)) {
            throw new CFGAlgorithmsException("El elemento no pertenece a la gramátic");
        }

        terminales.remove(terminal);

        //eliminamos producciones q tengan el terminal
        for (Set<String> prods : producciones.values()) {
            prods.removeIf(produccion -> produccion.indexOf(terminal) != -1);
        }
    }



    /**
     * Método que devuelve un conjunto con todos los símbolos terminales de la
     * gramática.
     *
     * @return Un conjunto con los terminales definidos.
     */
    public Set<Character> getTerminals() {
         return new HashSet<>(terminales);
    }



    /**
     * Método que indica, de los elementos no terminales, cuál es el axioma de
     * la gramática.
     *
     * @param nonterminal Por ejemplo, 'S'
     *
     * @throws CFGAlgorithmsException Si el elemento insertado no forma parte
     *                                del conjunto de elementos no terminales.
     */
    public void setStartSymbol(char nonterminal) throws CFGAlgorithmsException {
        // Ver si pertenece a no terminales
        if (!noTerminales.contains(nonterminal)) {
            throw new CFGAlgorithmsException("El elemento no forma parte del conjunto de los no terminales");
        }

        simboloInicio = nonterminal;
    }



    /**
     * Método que devuelve el axioma de la gramática.
     *
     * @return El axioma de la gramática
     *
     * @throws CFGAlgorithmsException Si el axioma todavía no ha sido
     *                                establecido.
     */
    public Character getStartSymbol() throws CFGAlgorithmsException {
        if (simboloInicio == null) {
            throw new CFGAlgorithmsException("El axioma todavía no existe.");
        }
        
        return simboloInicio;
    }



    /**
     * Método utilizado para construir la gramática. Admite producciones de tipo
     * 2. También permite añadir producciones a lambda (lambda se representa con
     * el caracter 'l' -- ele minúscula). Se permite añadirla en cualquier no
     * terminal.
     *
     * @param nonterminal A
     * @param production  Conjunto de elementos terminales y no terminales.
     *
     * @throws CFGAlgorithmsException Si está compuesta por elementos
     *                                (terminales o no terminales) no definidos previamente.
     */
    public void addProduction(char nonterminal, String production) throws CFGAlgorithmsException {

       if (!noTerminales.contains(nonterminal)) {
            throw new CFGAlgorithmsException("El no terminal no forma parte del conjunto de no terminales");
        }
        for (int i = 0; i < production.length(); i++) {
            char c = production.charAt(i);
            if (c!='l' && !terminales.contains(c) && !noTerminales.contains(c)) {
                throw new CFGAlgorithmsException("La producción tiene elementos que no existen");
            }
        }
        producciones.putIfAbsent(nonterminal, new HashSet<>());  // Asegura que hay un conjunto para ese no terminal
        
        //buscador invertido que nos recomendo Saugar
        Set<String> prodSet = producciones.get(nonterminal);
        //uso del buscador
        if (prodSet.contains(production)){
            throw new CFGAlgorithmsException("La prod ya existe este no terminal");
        }
        prodSet.add(production);  // Añade la producción al conjunto
        
        
    }



    /**
     * Elimina la producción indicada del elemento no terminal especificado.
     *
     * @param nonterminal Elemento no terminal al que pertenece la producción
     * @param production  Producción a eliminar
     *
     * @return True si la producción ha sido correctamente eliminada
     *
     * @throws CFGAlgorithmsException Si la producción no pertenecía a ese
     *                                elemento no terminal.
     */
    public boolean removeProduction(char nonterminal, String production) throws CFGAlgorithmsException {
        if (!noTerminales.contains(nonterminal)) {
            throw new CFGAlgorithmsException("El no terminal no está en la gramática");
        }

        // Metodo de busqueda invertido que nos dijo Saugar
        Set<String> prodSet = producciones.get(nonterminal);
        if (prodSet == null || !prodSet.contains(production)) {
            throw new CFGAlgorithmsException("La producción no pertenece a ese no terminal (remove prod)");
        }

        // Intenta eliminar la producción del conjunto
        boolean eliminado = prodSet.remove(production);

        // Verifica si el conjunto de producciones ha quedado vacío y elimina el no terminal del mapa si es necesario
        if (eliminado && prodSet.isEmpty()) {
            producciones.remove(nonterminal);
        }

        return eliminado;
    }



    /**
     * Devuelve una lista de String que representan todas las producciones que
     * han sido agregadas a un elemento no terminal.
     *
     * @param nonterminal Elemento no terminal del que se buscan las
     *                    producciones
     *
     * @return Devuelve una lista de String donde cada String es la parte
     *         derecha de cada producción
     */
    public List<String> getProductions(char nonterminal) {
        return new ArrayList<>(producciones.getOrDefault(nonterminal, new HashSet<>()));
    }



    /**
     * Devuelve un String que representa todas las producciones que han sido
     * agregadas a un elemento no terminal.
     *
     * @param nonterminal
     *
     * @return Devuelve un String donde se indica, el elemento no terminal, el
     *         símbolo de producción "::=" y las producciones agregadas separadas, única
     *         y exclusivamente por una barra '|' (no incluya ningún espacio). Por
     *         ejemplo, si se piden las producciones del elemento 'S', el String de
     *         salida podría ser: "S::=aBb|bC|dC". Las producciones DEBEN IR ORDENADAS
     *         POR ORDEN ALFABÉTICO.
     */
    public String getProductionsToString(char nonterminal) {
        
        //primero comprobamos si el no terminal tiene producciones para hacer el return vacio en caso de que lo esté y no dar un tostring con un mala estructura
        if (!producciones.containsKey(nonterminal) || producciones.get(nonterminal).isEmpty()) {
            return "";
        }
        Set<String> productionSet = producciones.get(nonterminal);

        List<String> productionList = new ArrayList<>(productionSet);

        Collections.sort(productionList);

        StringBuilder result = new StringBuilder(nonterminal + "::=");

        // Unimos las prods separadas con "|"
        for (int i = 0; i < productionList.size(); i++) {
            if (i > 0) {
                result.append("|");
            }
            result.append(productionList.get(i));
        }
        
        return result.toString();

    }



    /**
     * Devuelve un String con la gramática completa. Todos los elementos no
     * terminales deberán aparecer por orden alfabético (A,B,C...).
     *
     * @return Devuelve el agregado de hacer getProductionsToString sobre todos
     *         los elementos no terminales ORDENADOS POR ORDEN ALFABÉTICO.
     */
    public String getGrammar() {
        StringBuilder grammar = new StringBuilder();
        
        List<Character> noTerminalesOrdenados = new ArrayList<>(noTerminales);
        Collections.sort(noTerminalesOrdenados);
        for (Character nonTerminal : noTerminalesOrdenados){
            grammar.append(nonTerminal).append(" ::= ");
            
            List<String> produccionesOrdenadas = new ArrayList<>(producciones.get(nonTerminal));
            Collections.sort(produccionesOrdenadas);
            grammar.append(String.join(" | ", produccionesOrdenadas));
            grammar.append("\n");
        }
        return grammar.toString();
    }



    /**
     * Elimina todos los elementos que se han introducido hasta el momento en la
     * gramática (elementos terminales, no terminales, axioma y producciones),
     * dejando el algoritmo listo para volver a insertar una gramática nueva.
     */
    public void deleteGrammar() {
        noTerminales.clear();
        terminales.clear();
        producciones.clear();
        simboloInicio = null;
    }



    /**
     * Método que comprueba si la gramática dada de alta es una gramática
     * independiente del contexto.
     *
     * @return true Si la gramática es una gramática independiente del contexto.
     */
    public boolean isCFG() {
         for (Map.Entry<Character, Set<String>> entry : producciones.entrySet()) {
        // solo debe tener unn no terminal como clave
        if (!noTerminales.contains(entry.getKey())) {
            return false;
// Si hay alguna clave que no es no terminal no es CFG
        }
    }
    return true;
    }



    /**
     * Método que comprueba si la gramática almacenada tiene reglas innecesarias
     * (A::=A).
     *
     * @return True si contiene ese tipo de reglas
     */
    public boolean hasUselessProductions() {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    /**
     * Método que elimina las reglas innecesarias de la gramática almacenada.
     *
     * @return Devuelve una lista de producciones (un String de la forma "A::=A"
     *         por cada producción), con todas las reglas innecesarias
     *         eliminadas.
     */
    public List<String> removeUselessProductions() {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    /**
     * Método que elimina los símbolos inútiles de la gramática almacenada.
     *
     * @return Devuelve una lista con todos los símbolos no terminales y
     *         terminales eliminados.
     */
    public List<Character> removeUselessSymbols() {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    /**
     * Método que comprueba si la gramática almacenada tiene reglas no
     * generativas (reglas lambda). Excepto S::=l si sólo es para reconocer la
     * palabra vacía.
     *
     * @return True si contiene ese tipo de reglas
     */
    public boolean hasLambdaProductions() {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    /**
     * Método que elimina todas las reglas no generativas de la gramática
     * almacenada. La única regla que puede quedar es S::=l y debe haber sido
     * sustituida (y, por lo tanto, devuelta en la lista de producciones
     * "eliminadas").
     *
     * @return Devuelve una lista de no terminales que tenían reglas no
     *         generativas y han sido tratadas.
     */
    public List<Character> removeLambdaProductions() {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    /**
     * Método que comprueba si la gramática almacenada tiene reglas unitarias
     * (A::=B).
     *
     * @return True si contiene ese tipo de reglas
     */
    public boolean hasUnitProductions() {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    /**
     * Método que elimina las reglas unitarias de la gramática almacenada.
     *
     * @return Devuelve una lista de producciones (un String de la forma "A::=B"
     *         por cada producción), con todas las reglas unitarias eliminadas.
     */
    public List<String> removeUnitProductions() {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    /**
     * Método que transforma la gramática almacenada en una gramática bien
     * formada:
     * - 1. Elimina las reglas innecesarias.
     * - 2. Elimina las reglas no generativas.
     * - 3. Elimina las reglas unitarias.
     * - 4. Elimina los símbolo inútiles.
     */
    public void transformToWellFormedGrammar() {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



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
    public void checkCNFProduction(char nonterminal, String production) throws CFGAlgorithmsException {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    /**
     * Método que comprueba si la gramática dada de alta se encuentra en Forma
     * Normal de Chomsky. Es una precondición para la aplicación del algoritmo
     * CYK.
     *
     * @return true Si la gramática está en Forma Normal de Chomsky
     */
    public boolean isCNF() {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    /**
     * Método que transforma la gramática almacenada en su Forma Normal de
     * Chomsky equivalente.
     *
     * @throws CFGAlgorithmsException Si la gramática de la que partimos no es
     *                                una gramática bien formada.
     */
    public void transformIntoCNF() throws CFGAlgorithmsException {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    /**
     * Método que indica si una palabra pertenece al lenguaje generado por la
     * gramática que se ha introducido. Se utilizará el algoritmo CYK para
     * decidir si la palabra pertenece al lenguaje.
     *
     * La gramática deberá estar en FNC.
     *
     * @param word La palabra a verificar, tiene que estar formada sólo por
     *             elementos no terminales.
     *
     * @return TRUE si la palabra pertenece, FALSE en caso contrario
     *
     * @throws CFGAlgorithmsException Si la palabra proporcionada no está
     *                                formada sólo por terminales, si está formada por terminales que no
     *                                pertenecen al conjunto de terminales definido para la gramática
     *                                introducida, si la gramática es vacía o si el autómata carece de axioma.
     */
    public boolean isDerivedUsignCYK(String word) throws CFGAlgorithmsException {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }



    /**
     * Método que, para una palabra, devuelve un String que contiene todas las
     * celdas calculadas por el algoritmo CYK (la visualización debe ser similar
     * al ejemplo proporcionado en el PDF que contiene el paso a paso del
     * algoritmo).
     *
     * @param word La palabra a verificar, tiene que estar formada sólo por
     *             elementos no terminales.
     *
     * @return Un String donde se vea la tabla calculada de manera completa,
     *         todas las celdas que ha calculado el algoritmo.
     *
     * @throws CFGAlgorithmsException Si la palabra proporcionada no está
     *                                formada sólo por terminales, si está formada por terminales que no
     *                                pertenecen al conjunto de terminales definido para la gramática
     *                                introducida, si la gramática es vacía o si carece de axioma.
     */
    public String algorithmCYKStateToString(String word) throws CFGAlgorithmsException {
        throw new UnsupportedOperationException("Not supported yet."); // Generated from nbfs://nbhost/SystemFileSystem/Templates/Classes/Code/GeneratedMethodBody
    }

}
