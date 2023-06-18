; ********************************
; TEMPLATES
; ********************************
(deftemplate client
    (slot id (type INTEGER))
    (slot lat (type FLOAT))
    (slot long (type FLOAT))
)

(deftemplate taxi
    (slot id (type INTEGER))
    (slot occupied (type STRING))
)

(deftemplate taxi_location
    (slot id (type INTEGER))
    (slot long (type FLOAT))
    (slot lat (type FLOAT))
    (slot timestamp (type INTEGER))
)

(deftemplate taxi_destination
    (slot id (type INTEGER))
    (slot long (type FLOAT))
    (slot lat (type FLOAT))
)

(deftemplate station    
    (slot name (type STRING)) 
    (slot long (type FLOAT))
    (slot lat (type FLOAT))
    (slot slots (type INTEGER) (default 0))
    (slot max_slots (type INTEGER) (default 2))
)

; ********************************
; FACTS
; ********************************
(deffacts main_facts
    ; ********************************
    ; TAXIS
    ; ********************************
    (taxi
        (id 1)
        (occupied "FALSE")
    )

    (taxi_location
        (id 1)
        (lat 0.0)
        (long 0.0)
        (timestamp 0)
    )
    

    (taxi
        (id 2)
        (occupied "FALSE")
    )

    (taxi_location
        (id 2)
        (long 0.0) 
        (lat 50.0)
        (timestamp 0)
    )

    (taxi
        (id 3)
        (occupied "FALSE")
    )

    (taxi_location
        (id 3)
        (long 50.0) 
        (lat 0.0)
        (timestamp 0)
    )

    (taxi
        (id 4)
        (occupied "FALSE")       
    )

    (taxi_location
        (id 4)
        (long 50.0)
        (lat 50.0)
        (timestamp 0)
    )

    ; ********************************
    ; STATIONS
    ; ********************************
    
    (station    
        (name "Welcome boulevard") 
        (long 20.0)
        (lat 35.0)
        (slots 0)
    )

    (station    
        (name "Boulevard of the dead")
        (long 15.0)
        (lat 10.0)
        (slots 0)
    )

    (station
        (name "New York street") 
        (long 40.0)
        (lat 20.0)
        (slots 0)
    )

    ; ********************************
    ; CLIENTS
    ; ********************************
    (client
        (id 1)
        (long 10.0)
        (lat 40.0)
    )

    (client
        (id 2)
        (long 40.0)
        (lat 20.0)
    )
)

; ********************************
; FUNCTIONS
; ********************************

; ; Función para esperar un tiempo en segundos
; (deffunction wait (?s)
;     (bind ?test "TRUE")
;     (bind ?start_time (time))
;     (while (eq ?test "TRUE")
;         (bind ?current_time (time))
;         (if (> (- ?current_time ?start_time) ?s)
;             then
;                 (bind ?test "FALSE")
;         )
;     )
; )

; Función para calcular la distancia manhattan entre dos puntos
(deffunction distance (?x1 ?y1 ?x2 ?y2)
   (+ (abs (- ?x2 ?x1)) (abs (- ?y2 ?y1)))
)

; Función para mover un taxi en el eje x
(deffunction move_on_x (?x ?x1 ?y1 ?ts ?tl)
    (if (> ?x1 ?x)
        then
            (modify ?tl (long (- ?x1 1)) (timestamp (+ ?ts 1)))
            ; (wait 0.1)
            (return (- ?x1 1))
        else
            (modify ?tl (long (+ ?x1 1)) (timestamp (+ ?ts 1)))
            ; (wait 0.1)
            (return (+ ?x1 1))
    )
)

; Función para mover un taxi en el eje y
(deffunction move_on_y (?x1 ?y ?y1 ?ts ?tl)
    (if (> ?y1 ?y)
        then
            (modify ?tl (lat (- ?y1 1)) (timestamp (+ ?ts 1)))
            ; (wait 0.1)
            (return (- ?y1 1))
        else
            (modify ?tl (lat (+ ?y1 1)) (timestamp (+ ?ts 1)))
            ; (wait 0.1)
            (return (+ ?y1 1))
    )
)

; ********************************
; RULES
; ********************************

; Regla para modificar el destino de un cliente esperando si se recibe una segunda llamada del mismo.
(defrule modify_client_waiting
    (declare (salience 200))
    ?cc <- (client_calling ?i ?dx ?dy)
    ?cw <- (client_waiting ?c ?t ?wx ?wy) 
    (test (eq (fact-slot-value ?c id) ?i))
    =>
    (assert (client_waiting ?c ?t ?dx ?dy))
    (printout t "Client-" ?i " destination has been modified to (" ?dx "," ?dy ")." crlf)
    (retract ?cw)
    (retract ?cc)
)

; Regla cliente llama a un taxi
(defrule client_calling_from
    (declare (salience 120))
    ?cc <- (client_calling ?i ?dx ?dy)
    ?c <- (client (id ?i) (long ?cx) (lat ?cy))
    =>
    (assert (client_calling_from ?c ?dx ?dy))
    (printout t "Client-" ?i )
    (bind ?test 0)
    (do-for-all-facts ((?s station))
        (and (eq (fact-slot-value ?s long) ?cx) (eq (fact-slot-value ?s lat) ?cy))
        (printout t " calling from " (fact-slot-value ?s name))
        (bind ?test 1)
    )
    (if (eq ?test 0)
        then
            (printout t " calling from (" ?cx "," ?cy ")")
    )
    (do-for-all-facts ((?s station))
        (and (eq (fact-slot-value ?s long) ?dx) (eq (fact-slot-value ?s lat) ?dy))
        (printout t "  to go to " (fact-slot-value ?s name) "." crlf)
        (bind ?test 2)
    )
    (if (< ?test 2)
        then
            (printout t " to go to (" ?dx "," ?dy ")." crlf)
    )
    (retract ?cc)
)

; Regla asignar taxi disponible más cercano al cliente
(defrule assing_closest_available_taxi_to_client_calling
    (declare (salience 70))
    ?cc <- (client_calling_from ?c ?dx ?dy)
    (exists (taxi (occupied "FALSE")))
    =>
    (bind ?min_dist 10000)
    (do-for-all-facts ((?t taxi))
        (eq ?t:occupied "FALSE")
        (do-for-all-facts ((?tl taxi_location))
            (eq ?t:id ?tl:id)
            (bind ?dist (distance (fact-slot-value ?c long) (fact-slot-value ?c lat) ?tl:long ?tl:lat))
            (if (< ?dist ?min_dist)
                then
                    (bind ?min_dist ?dist)
                    (bind ?closest_taxi ?t)
            )
        )
    )
    (assert (client_waiting ?c ?closest_taxi ?dx ?dy))
    (modify ?closest_taxi (occupied "TRUE"))
    (assert (taxi_destination (id (fact-slot-value ?closest_taxi id)) (long (fact-slot-value ?c long)) (lat (fact-slot-value ?c lat))))
    (printout t "Taxi " (fact-slot-value ?closest_taxi id) " going for Client-" (fact-slot-value ?c id) crlf)
    (printout t "Distance to taxi " (fact-slot-value ?closest_taxi id) ": " ?min_dist crlf)
    (retract ?cc)
)

; Regla cobro cliente
(defrule charge_client
    (declare (salience 70))
    ?t <- (taxi (id ?ti))
    (taxi_location (id ?ti) (long ?lx) (lat ?ly))
    (taxi_destination (id ?ti) (long ?tdx) (lat ?tdy))
    ?cc <- (client_catched ?c ?ti)
    =>
    (bind ?price 2) ; MAX PRICE
    (do-for-all-facts ((?s station))
        (and (eq (fact-slot-value ?c long) (fact-slot-value ?s long)) (eq (fact-slot-value ?c lat) (fact-slot-value ?s lat)))
        (bind ?price (- ?price 1))
    )
    (if (< (distance (fact-slot-value ?c long) (fact-slot-value ?c lat)  ?tdx ?tdy) 12)
        then
            (bind ?price (- ?price 1))
    )
    (if (eq ?price 0)
        then
            (printout t "Client-" (fact-slot-value ?c id) " bill will be cheap."crlf)
    )
    (if (eq ?price 1)
        then
            (printout t "Client-" (fact-slot-value ?c id) " bill will be medium."crlf)
    )
    (if (eq ?price 2)
        then
            (printout t "Client-" (fact-slot-value ?c id) " bill will be expensive."crlf)
    )
    (retract ?cc)
)

; Regla taxi libre sin estación acude a la más cercana
(defrule taxi_free_without_station_go_to_closest
    (declare (salience 60))
    ?t <- (taxi (id ?ti) (occupied "FALSE"))
    (taxi_location (id ?ti) (long ?lx) (lat ?ly))
    (not (taxi_in_station ?t ?st))
    (not (taxi_destination (id ?ti) (long ?dx) (lat ?dy)))
    =>
    (bind ?min_dist 10000)
    (do-for-all-facts ((?s station))
        (< (fact-slot-value ?s slots) (fact-slot-value ?s max_slots))
        (bind ?dist (distance ?lx ?ly ?s:long ?s:lat))
        (if (< ?dist ?min_dist)
            then
                (bind ?min_dist ?dist)
                (bind ?closest_station ?s)
        )
    )
    (assert(taxi_destination (id ?ti) (long (fact-slot-value ?closest_station long)) (lat (fact-slot-value ?closest_station lat))))
    (printout t "Free taxi " ?ti ", in comming to " (fact-slot-value ?closest_station name) crlf)
    (printout t "Distance to station " (fact-slot-value ?closest_station name) ": " ?min_dist crlf)
)

; Regla actualizar la posición de un cliente en un taxi
(defrule update_client_location
    (declare (salience 60))
    ?cl <- (client_in_taxi ?t ?c)
    ?tl <- (taxi_location (id ?ti) (long ?x1) (lat ?y1) (timestamp ?ts))
    (test (eq (fact-slot-value ?t id) ?ti))
    (test (or(not(eq ?x1 (fact-slot-value ?c long))) (not(eq ?y1 (fact-slot-value ?c lat)))))
    =>
    (modify ?c (long ?x1) (lat ?y1))
)

; Regla taxi recoge cliente
(defrule taxi_catch_client
    (declare (salience 60))
    ?cw <- (client_waiting ?c ?t ?dx ?dy)
    ?tl <- (taxi_location (id ?ti) (long ?lx) (lat ?ly))
    ?td <- (taxi_destination (id ?ti) (long ?tdx) (lat ?tdy))
    (test (eq ?ti (fact-slot-value ?t id)))
    (test (and (eq ?lx (fact-slot-value ?c long)) (eq ?ly (fact-slot-value ?c lat))))
    =>
    (assert (client_in_taxi ?t ?c))
    (assert (client_catched ?c ?ti))
    (modify ?td (long ?dx) (lat ?dy))
    (printout t "Taxi " ?ti " catched Client-" (fact-slot-value ?c id) crlf)
    (retract ?cw)
)

; Regla cliente llega al destino
(defrule client_arrives_destination
    (declare (salience 55))
    ?ct <- (client_in_taxi ?t ?c)
    ?tl <- (taxi_location (id ?ti) (long ?lx) (lat ?ly))
    ?td <- (taxi_destination (id ?ti) (long ?dx) (lat ?dy))
    (test (eq (fact-slot-value ?t id) ?ti))
    (test (and (= ?dx ?lx) (= ?dy ?ly)))
    =>
    (bind ?test 0)
    (do-for-all-facts ((?s station))
        (and (eq (fact-slot-value ?s long) ?lx) (eq (fact-slot-value ?s lat) ?ly))
        (modify ?t (occupied "FALSE"))
        (if (not(eq (fact-slot-value ?s slots) (fact-slot-value ?s max_slots)))
            then
                (modify ?s (slots (+ (fact-slot-value ?s slots) 1)))
                (printout t "Slots: " (fact-slot-value ?s slots) "/" (fact-slot-value ?s max_slots) crlf)
                (assert (taxi_in_station ?t ?s))
        )
        (printout t "Taxi " ?ti " arrived to " (fact-slot-value ?s name) "." crlf)
        (printout t "Client-" (fact-slot-value ?c id) " arrived to " (fact-slot-value ?s name) "." crlf)
        (retract ?ct)
        (retract ?td)
        (bind ?test 1)
    )
    (if (eq ?test 0)
        then
            (modify ?t (occupied "FALSE"))
            (printout t "Client-" (fact-slot-value ?c id) " arrived to (" ?dx "," ?dy ")." crlf)
            (retract ?ct)
            (retract ?td)
    )
)

; Regla taxi llega a la estación
(defrule taxi_arrives_station
    (declare (salience 50))
    ?t <- (taxi (id ?ti))
    (taxi_location (id ?ti) (long ?lx) (lat ?ly))
    ?td <- (taxi_destination (id ?ti) (long ?tdx) (lat ?tdy))
    (not (taxi_in_station ?t ?st))
    (test (and (eq ?tdx ?lx) (eq ?tdy ?ly)))
    =>
    (do-for-all-facts ((?st station))
        (and (eq ?st:long ?tdx) (eq ?st:lat ?tdy))
            (assert (taxi_in_station ?t ?st))
            (modify ?st (slots (+ (fact-slot-value ?st slots) 1)))
            (printout t "Taxi " ?ti " arrived to " (fact-slot-value ?st name) crlf)
            (printout t "Slots: " (fact-slot-value ?st slots) "/" (fact-slot-value ?st max_slots) crlf)
            (retract ?td)
    )
)

; Regla taxi sale de la estación
(defrule taxi_leaves_station
    (declare (salience 50))
    ?ts <-(taxi_in_station ?t ?st)
    (taxi_location (id ?ti) (long ?lx) (lat ?ly))
    (test (eq ?ti (fact-slot-value ?t id)))
    (test (or (not (eq (fact-slot-value ?st long) ?lx)) (not (eq (fact-slot-value ?st lat) ?ly))))
    =>
    (modify ?st (slots (- (fact-slot-value ?st slots) 1)))
    (printout t "Taxi " (fact-slot-value ?t id) " left " (fact-slot-value ?st name) "." crlf)
    (printout t "Slots: " (fact-slot-value ?st slots) "/" (fact-slot-value ?st max_slots) crlf)
    (retract ?ts)
)

; Regla mostrar posición del taxi
(defrule show_taxi_location
    (declare (salience 40))
    ?tl <- (taxi_location (id ?ti) (long ?lx) (lat ?ly) (timestamp ?ts))
    (test(> ?ts 10))
    =>
    (modify ?tl (timestamp 0))
    (printout t "Taxi " ?ti " is in " ?lx " " ?ly "." crlf)
)

; Regla movimiento taxi a estación
(defrule move_taxi_to_station
    (declare (salience 30))
    (taxi (id ?ti))
    ?tl <- (taxi_location (id ?ti) (long ?lx) (lat ?ly) (timestamp ?ts))
    (taxi_destination (id ?ti) (long ?tdx) (lat ?tdy))
    (station (name ?n) (long ?tdx) (lat ?tdy) (slots ?s) (max_slots ?ms))
    (test(< ?s ?ms))
    (test (or (not (eq ?tdx ?lx)) (not (eq ?tdy ?ly))))
    =>
    (if (and (eq ?tdx ?lx) (not(eq ?tdy ?ly)))
        then
            (bind ?ly (move_on_y ?lx ?tdy ?ly ?ts ?tl))
        else
            (bind ?lx (move_on_x ?tdx ?lx ?ly ?ts ?tl))
    )
)

; Regla movimiento taxi a cliente
(defrule move_taxi_to_client
    (declare (salience 30))
    ?t <- (taxi (id ?ti))
    ?tl <- (taxi_location (id ?ti) (long ?lx) (lat ?ly) (timestamp ?ts))
    (taxi_destination (id ?ti) (long ?tdx) (lat ?tdy))
    (client_waiting ?c ?t ?dx ?dy)
    (test (or (not (eq ?tdx ?lx)) (not (eq ?tdy ?ly))))
    =>
    (if (and (eq ?tdx ?lx) (not(eq ?tdy ?ly)))
        then
            (bind ?ly (move_on_y ?lx ?tdy ?ly ?ts ?tl))
        else
            (bind ?lx (move_on_x ?tdx ?lx ?ly ?ts ?tl))
    )
)

; Regla movimiento cliente a destino
(defrule move_client_to_destination
    (declare (salience 30))
    ?t <- (taxi (id ?ti))
    ?tl <- (taxi_location (id ?ti) (long ?lx) (lat ?ly) (timestamp ?ts))
    (taxi_destination (id ?ti) (long ?tdx) (lat ?tdy))
    (client_in_taxi ?t ?c)
    (test (or (not (eq ?tdx ?lx)) (not (eq ?tdy ?ly))))
    =>
    (if (and (eq ?tdx ?lx) (not(eq ?tdy ?ly)))
        then
            (bind ?ly (move_on_y ?lx ?tdy ?ly ?ts ?tl))
        else
            (bind ?lx (move_on_x ?tdx ?lx ?ly ?ts ?tl))
    )
)
