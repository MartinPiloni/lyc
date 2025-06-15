# Laboratorio Lenguajes y Compiladores 2025 

En este proyecto se implementa la semántica denotacional para un lenguaje imperativo simple. 

El laboratorio 1 incluye soporte para variables, expresiones enteras y booleanas, estructuras de control como `if`, `while`, manejo de errores y variables locales.
En el laboratorio 2 se extiende el primer laboratorio agregando input/output.

## Ejemplos incluidos
### Lab1
#### División con resto
Calcula la división entera a / b. Devuelve el cociente en `x` y el resto en `y`.
Si `x < 0` o `y <= 0`, aborta dejando los valores iniciales de `x` e `y`.

Ejemplo de ejecución
```
> ejemploDivMod 5 2 
x vale 2
y vale 1
```

### Lab2
#### Factorial
Calcula el factorial de un número `x` ingresado por consola. Si el número ingresado es negativo, el programa aborta.

Ejemplo de ejecución
```
> factorial
5
120
```

#### Suma Gaussiana
Calcula la suma de todos los enteros desde 1 hasta `n`, donde `n` es un numero ingresado por consola. Si el número ingresado es negativo, el programa aborta.

Ejemplo de ejecución
```
> sumGauss
10 
55
```
