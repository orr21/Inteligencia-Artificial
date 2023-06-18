% Añadiremos las asignaturas de música (mus) e inglés (ing).
% Añadiremos también el jueves.
% A primera hora nunca puede haber ni matemáticas ni lengua.
% Los jueves siempre debe haber una hora de música.
% Matemáticas y lengua no debe coincidir el mismo día. Podemos utilizar el operador \+ para negar una condición.

%
%       GENERADOR DE HORARIOS DE CLASE
%

asignatura(mat).
asignatura(len).
asignatura(nat).
asignatura(bio).
asignatura(mus).
asignatura(ing).


diferente(A,B,C,D) :-
    dif(A,B),
    dif(A,C),
    dif(A,D),
    dif(B,C),
    dif(B,D),
    dif(C,D).

horario(L1,L2,L3,L4, M1,M2,M3,M4, X1,X2,X3,X4, J1,J2,J3,J4) :-
    % LUNES
    asignatura(L1), dif(L1,mat),dif(L1,len), % Los lunes a primera no puede haber matemáticas.
    asignatura(L2),
    asignatura(L3),
    asignatura(L4),
    \+ ((L2 == mat;L3 == mat;L4 == mat),(L2 == len; L3 == len; L4 == len)), % No puede haber matemáticas y lengua el mismo día.
    diferente(L1,L2,L3,L4), % No puede repetirse una asignatura el mismo día.
    % MARTES
    asignatura(M1), dif(M1,mat),dif(M1,len),
    asignatura(M2),
    asignatura(M3),
    asignatura(M4),
    \+ ((M2 == mat;M3 == mat;M4 == mat),(M2 == len; M3 == len; M4 == len)), % No puede haber matemáticas y lengua el mismo día.
    diferente(M1,M2,M3,M4),
    % MIÉRCOLES
    asignatura(X1), dif(X1,mat),dif(X1,len),
    asignatura(X2),
    asignatura(X3),
    asignatura(X4),
    \+ ((X2 == mat;X3 == mat;X4 == mat),(X2 == len; X3 == len; X4 == len)), % No puede haber matemáticas y lengua el mismo día.
    diferente(X1,X2,X3,X4),
    % JUEVES
    asignatura(J1), dif(J1,mat),dif(J1,len),
    asignatura(J2),
    asignatura(J3),
    asignatura(J4),
    \+ ((J2 == mat;J3 == mat;J4 == mat),(J2 == len; J3 == len; J4 == len)), % No puede haber matemáticas y lengua el mismo día.
    (J1 == mus; J2 == mus; J3 == mus; J4 == mus), % Debe haber una hora de Música los jueves.
    diferente(J1,J2,J3,J4).


go(L1,L2,L3,L4,M1,M2,M3,M4,X1,X2,X3,X4,J1,J2,J3,J4) :-
    horario(L1,L2,L3,L4,M1,M2,M3,M4,X1,X2,X3,X4,J1,J2,J3,J4),
    writeln(" L   M   X  J"),
    writeln("-----------"),
    write(L1),
    write(" "),
    write(M1),
    write(" "),
    write(X1),
    write(" "),
    writeln(J1),
    
    write(L2),
    write(" "),
    write(M2),
    write(" "),
    write(X2),
    write(" "),
    writeln(J2),
    
    write(L3),
    write(" "),
    write(M3),
    write(" "),
    write(X3),
    write(" "),
    write(J3),
    writeln(" "),

    write(L4),
    write(" "),
    write(M4),
    write(" "),
    write(X4),
    write(" "),
    write(J4),
    writeln(" "),
    writeln(" ").
