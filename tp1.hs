--import Test.HUnit
{-- Tipos --}

import Data.Either
import Data.List

data Dirección = Norte | Sur | Este | Oeste
  deriving (Eq, Show)
type Posición = (Float, Float)

data Personaje = Personaje Posición String  -- posición inicial, nombre
  | Mueve Personaje Dirección               -- personaje que se mueve, dirección en la que se mueve
  | Muere Personaje                         -- personaje que muere
  deriving (Eq, Show)

data Objeto = Objeto Posición String        -- posición inicial, nombre
  | Tomado Objeto Personaje                 -- objeto que es tomado, personaje que lo tomó
  | EsDestruido Objeto                      -- objeto que es destruido
  deriving (Eq, Show)
 
type Universo = [Either Personaje Objeto]

{-- Observadores y funciones básicas de los tipos --}
siguiente_posición :: Posición -> Dirección -> Posición
siguiente_posición p Norte = (fst p, snd p + 1)
siguiente_posición p Sur = (fst p, snd p - 1)
siguiente_posición p Este = (fst p + 1, snd p)
siguiente_posición p Oeste = (fst p - 1, snd p)

posición :: Either Personaje Objeto -> Posición
posición (Left p) = posición_personaje p
posición (Right o) = posición_objeto o

posición_objeto :: Objeto -> Posición
posición_objeto = foldObjeto const (const posición_personaje) id

nombre :: Either Personaje Objeto -> String
nombre (Left p) = nombre_personaje p
nombre (Right o) = nombre_objeto o

nombre_personaje :: Personaje -> String
nombre_personaje = foldPersonaje (const id) const id

está_vivo :: Personaje -> Bool
está_vivo = foldPersonaje (const (const True)) (const (const True)) (const False)

fue_destruido :: Objeto -> Bool
fue_destruido = foldObjeto (const (const False)) const (const True)

universo_con :: [Personaje] -> [Objeto] -> [Either Personaje Objeto]
universo_con ps os = map Left ps ++ map Right os

es_un_objeto :: Either Personaje Objeto -> Bool
es_un_objeto (Left o) = False
es_un_objeto (Right p) = True

es_un_personaje :: Either Personaje Objeto -> Bool
es_un_personaje (Left o) = True
es_un_personaje (Right p) = False

-- Asume que es un personaje
personaje_de :: Either Personaje Objeto -> Personaje
personaje_de (Left p) = p

-- Asume que es un objeto
objeto_de :: Either Personaje Objeto -> Objeto
objeto_de (Right o) = o

en_posesión_de :: String -> Objeto -> Bool
en_posesión_de n = foldObjeto (const (const False)) (\ r p -> nombre_personaje p == n) (const False)

objeto_libre :: Objeto -> Bool
objeto_libre = foldObjeto (const (const True)) (const (const False)) (const False)

norma2 :: (Float, Float) -> (Float, Float) -> Float
norma2 p1 p2 = sqrt ((fst p1 - fst p2) ^ 2 + (snd p1 - snd p2) ^ 2)

cantidad_de_objetos :: Universo -> Int
cantidad_de_objetos = length . objetos_en

cantidad_de_personajes :: Universo -> Int
cantidad_de_personajes = length . personajes_en

distancia :: (Either Personaje Objeto) -> (Either Personaje Objeto) -> Float
distancia e1 e2 = norma2 (posición e1) (posición e2)

objetos_libres_en :: Universo -> [Objeto]
objetos_libres_en u = filter objeto_libre (objetos_en u)

está_el_personaje :: String -> Universo -> Bool
está_el_personaje n = foldr (\x r -> es_un_personaje x && nombre x == n && (está_vivo $ personaje_de x) || r) False

está_el_objeto :: String -> Universo -> Bool
está_el_objeto n = foldr (\x r -> es_un_objeto x && nombre x == n && not (fue_destruido $ objeto_de x) || r) False

-- Asume que el personaje está
personaje_de_nombre :: String -> Universo -> Personaje
personaje_de_nombre n u = foldr1 (\x1 x2 -> if nombre_personaje x1 == n then x1 else x2) (personajes_en u)

-- Asume que el objeto está
objeto_de_nombre :: String -> Universo -> Objeto
objeto_de_nombre n u = foldr1 (\x1 x2 -> if nombre_objeto x1 == n then x1 else x2) (objetos_en u)

es_una_gema :: Objeto -> Bool
es_una_gema o = isPrefixOf "Gema de" (nombre_objeto o)

{-Ejercicio 1-}

foldPersonaje :: (Posición -> String -> a) -> (a -> Dirección -> a) -> (a -> a) -> Personaje -> a
foldPersonaje f1 f2 f3 p = case p of
                  Personaje pos str -> f1 pos str
                  Mueve p' d -> f2 (rec p') d
                  Muere p' -> f3 (rec p')
                  where rec = foldPersonaje f1 f2 f3

foldObjeto :: (Posición -> String -> a) -> (a -> Personaje -> a) -> (a -> a) -> Objeto -> a
foldObjeto f1 f2 f3 obj = case obj of
                  Objeto pos str -> f1 pos str
                  Tomado obj p -> f2 (rec obj) p 
                  EsDestruido obj' -> f3 (rec obj')
                  where rec = foldObjeto f1 f2 f3

{-Ejercicio 2-}


-- f1 es id porque, si es Personaje, quiero que me devuelva la posición actual
-- f2 es la funcion que se aplica a Mueve. Quiero que sea siguiente_posicion
-- f3 es id porque, si es Muere, quiero que me devuelva la posición actual
posición_personaje :: Personaje -> Posición
posición_personaje = foldPersonaje (\pos _ -> pos)
                                    (\pers direccion -> siguiente_posición pers direccion) 
                                    (\pers -> posición pers)

-- f1 es id porque, si es Objeto, quiero que me devuelva el nombre actual
nombre_objeto :: Objeto -> String
nombre_objeto = foldObjeto (\_ str -> str)
                           (\obj _ -> nombre obj)  -- caso objeto tomado
                          (\obj -> nombre obj)      --caso objeto destruido

-- {-Ejercicio 3-}

objetos_en :: Universo -> [Objeto]
objetos_en = foldr (\x rec -> if es_un_objeto x then objeto_de x : rec else rec) []

{- Demostracion
∀ u :: Universo .∀ o :: Objeto . elem o (objetos_en u) ⇒ elem (Right o) u

Caso base: Como estamos recorriendo una lista, el unico constructor base es u=[]

P([]):
elem o (objetos_en []) ⇒ elem (Right o) []
elem o (foldr (\x rec -> if es_un_objeto x then objeto_de x : rec else rec) [] []) ⇒ elem (Right o) []
elem o [] ⇒ elem (Right o) []
False => elem (Right o) []
True

Caso inductivo: ∀ys::[Either Personaje Objeto] P(ys) => ∀y::Either Personaje Objeto P(y:ys)
La hipotesis inductiva HI es que vale P(ys) : ∀ys::[Either Personaje Objeto]. elem o (objetos_en (ys)) ⇒ elem (Right o) (ys)

Distinguimos dos casos:
1. `y` es el objeto que estamos buscando.
2. `y` es un objeto pero no el que estamos buscando.
3. `y` es un personaje.

1. Caso `y` es el objeto que estamos buscando:
  elem o (objetos_en (y:ys)) ⇒ elem (Right o) (y:ys)
          
  Right o == y || elem o (objetos_en (ys)) ⇒ elem (Right o) (y:ys)    -- VALIDAR ESTO!!!!!!!!
  True => elem (Right o) (y:ys)
  elem (Right o) (y:ys)
  Right o == y || elem (Right o) (ys)
  True

2. Caso `y` es un objeto pero no el que estamos buscando:
  elem o (objetos_en (y:ys)) ⇒ elem (Right o) (y:ys) 

  Vale que objetos_en (y:ys) = y : objetos_en ys, porque ...
  ...

  Entonces:
  elem o (objetos_en ys) ⇒ elem (Right o) (y:ys)

  Suponemos que vale elem o (objetos_en ys), sino es trivial.
  Nos queda ver que valga 

  elem (Right o) (y:ys) 
  Right o == y || elem (Right o) (ys)      -- pero sabemos que Right o != y
  elem (Right o) (ys)                      -- esto vale por HI: elem o (objetos_en (ys)) ⇒ elem (Right o) (ys)

3. Caso `y` es un personaje:
  elem o (objetos_en (y:ys)) ⇒ elem (Right o) (y:ys) 
  elem o (objetos_en ys) ⇒ elem (Right o) (y:ys)

  Suponeoms 
-}
                                    
personajes_en :: Universo -> [Personaje]
personajes_en = foldr (\x rec -> if es_un_personaje x then personaje_de x : rec else rec) []

-- {-Ejercicio 4-}

objetos_en_posesión_de ::  Personaje -> Universo -> [Objeto]
objetos_en_posesión_de p = foldr (\x rec -> if (es_un_objeto x && en_posesión_de (nombre_personaje p) (objeto_de x)) then (objeto_de x) : rec else rec) []  

-- {-Ejercicio 5-}

-- -- Asume que hay al menos un objeto
objeto_libre_mas_cercano :: Personaje -> Universo -> Objeto
objeto_libre_mas_cercano p u = foldr1 (\obj rec -> if (objeto_libre obj && (distancia (Left p) (Right obj) < distancia (Left p) (Right rec))) then obj else rec) (objetos_en u)

-- {-Ejercicio 6-}
-- Devuelve true si tiene 6 o mas
tiene_thanos_todas_las_gemas :: Universo -> Bool
tiene_thanos_todas_las_gemas u = length (filter (\obj -> (es_una_gema obj) && (en_posesión_de "Thanos" obj)) (objetos_en u)) >= 6

-- {-Ejercicio 7-}

-- esta_vivo_en_universo
esta_vivo_en_universo :: String -> Universo -> Bool
esta_vivo_en_universo str = foldr (\x rec -> if es_un_personaje x && nombre_personaje (personaje_de x) == str && está_vivo (personaje_de x) then True else rec) False

-- tiene_objeto_en_universo
tiene_objeto_en_universo :: Universo -> String -> String -> Bool
tiene_objeto_en_universo u nombreP nombreObj = foldr(\x rec -> if es_un_objeto x && nombre_objeto (objeto_de x) == nombreObj && en_posesión_de nombreP (objeto_de x) then True else rec) False u

-- falta chequeo de "esta vivo" y "esta destruido"
podemos_ganarle_a_thanos :: Universo -> Bool
podemos_ganarle_a_thanos u = not (tiene_thanos_todas_las_gemas u)
                          && ((esta_vivo_en_universo "Thor" u && está_el_objeto "Stormbreaker" u)
                              || (esta_vivo_en_universo "Wanda" u && esta_vivo_en_universo "Visión" u && tiene_objeto_en_universo u "Visión" "Gema de la Mente")
                              )

{-Tests-}

-- main :: IO Counts
-- main = do runTestTT allTests

-- allTests = test [ -- Reemplazar los tests de prueba por tests propios
--   "ejercicio1" ~: testsEj1,
--   "ejercicio2" ~: testsEj2,
--   "ejercicio3" ~: testsEj3,
--   "ejercicio4" ~: testsEj4,
--   "ejercicio5" ~: testsEj5,
--   "ejercicio6" ~: testsEj6,
--   "ejercicio7" ~: testsEj7
--   ]

-- phil = Personaje (0,0) "Phil"
-- mjölnir = Objeto (2,2) "Mjölnir"
-- universo_sin_thanos = universo_con [phil] [mjölnir]

-- testsEj1 = test [ -- Casos de test para el ejercicio 1
--   foldPersonaje (\p s -> 0) (\r d -> r+1) (\r -> r+1) phil             -- Caso de test 1 - expresión a testear
--     ~=? 0                                                               -- Caso de test 1 - resultado esperado
--   ,
--   foldPersonaje (\p s -> 0) (\r d -> r+1) (\r -> r+1) (Muere phil)     -- Caso de test 2 - expresión a testear
--     ~=? 1                                                               -- Caso de test 2 - resultado esperado
--   ]

-- testsEj2 = test [ -- Casos de test para el ejercicio 2
--   posición_personaje phil       -- Caso de test 1 - expresión a testear
--     ~=? (0,0)                   -- Caso de test 1 - resultado esperado
--   ]

-- testsEj3 = test [ -- Casos de test para el ejercicio 3
--   objetos_en []       -- Caso de test 1 - expresión a testear
--     ~=? []            -- Caso de test 1 - resultado esperado
--   ]

-- testsEj4 = test [ -- Casos de test para el ejercicio 4
--   objetos_en_posesión_de "Phil" []       -- Caso de test 1 - expresión a testear
--     ~=? []                             -- Caso de test 1 - resultado esperado
--   ]

-- testsEj5 = test [ -- Casos de test para el ejercicio 5
--   objeto_libre_mas_cercano phil [Right mjölnir]       -- Caso de test 1 - expresión a testear
--     ~=? mjölnir                                       -- Caso de test 1 - resultado esperado
--   ]

-- testsEj6 = test [ -- Casos de test para el ejercicio 6
--   tiene_thanos_todas_las_gemas universo_sin_thanos       -- Caso de test 1 - expresión a testear
--     ~=? False                                            -- Caso de test 1 - resultado esperado
--   ]

-- testsEj7 = test [ -- Casos de test para el ejercicio 7
--   podemos_ganarle_a_thanos universo_sin_thanos         -- Caso de test 1 - expresión a testear
--     ~=? False                                          -- Caso de test 1 - resultado esperado
--   ]
