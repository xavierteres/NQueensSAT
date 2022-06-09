%%%%%%%%%%%%
% sat(F,I,M)
% si F es satisfactible, M sera el model de F afegit a la interpretació I (a la primera crida I sera buida).
% Assumim invariant que no hi ha literals repetits a les clausules ni la clausula buida inicialment.
sat([],I,I):- write('SAT'),nl,!.
sat(CNF,I,M):-
    % Ha de triar un literal d’una clausula unitaria, si no n’hi ha cap, llavors un literal pendent qualsevol.
    decideix(CNF,Lit),
    % Simplifica la CNF amb el Lit triat (compte pq pot fallar, es a dir si troba la clausula buida fallara i fara backtraking).
    simplif(Lit,CNF,CNFS),
    % crida recursiva amb la CNF i la interpretacio actualitzada
    append([Lit],I,R),
    sat(CNFS,R,M).

%%%%%%%%%%%%%%%%%%
% decideix(F, Lit)
% Donat una CNF,
% -> el segon parametre sera un literal de CNF
%  - si hi ha una clausula unitaria sera aquest literal, sino
%  - un qualsevol o el seu negat.
decideix(F,Lit):- member([Lit],F), !. % si hi ha una clausula unitaria sera aquest literal (tallem les demés branques)
decideix([[Lit|_]|_],Lit). % el primer literal de la primera clàusula ("un qualsevol")
decideix([[Lit|_]|_],Negat) :- Negat is -Lit. % el negat del primer literal de la primera clàusula

%%%%%%%%%%%%%%%%%%%%%
% simlipf(Lit, F, FS)
% Donat un literal Lit i una CNF,
% -> el tercer parametre sera la CNF que ens han donat simplificada:
%  - sense les clausules que tenen lit
%  - treient -Lit de les clausules on hi es, si apareix la clausula buida fallara.
simplif(_,[],[]).
simplif(Lit,[X|Xs],FS):- append(_,[Lit|_],X), !, simplif(Lit, Xs, FS), !.
simplif(Lit,[X|Xs],FS):-
    Negat is -Lit,
    append(A,[Negat|B],X), !,
    append(A,B,R),
    R \= [],
    simplif(Lit, Xs, R1),
    append([R],R1,FS), !.
simplif(Lit,[X|Xs],FS):- simplif(Lit, Xs, R), append([X],R,FS), !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%
% comaminimUn(L,CNF)
% Donat una llista de variables booleanes,
% -> el segon parametre sera la CNF que codifica que com a minim una sigui certa.
comaminimUn(L,[L]).

%%%%%%%%%%%%%%%%%%%
% comamoltUn(L,CNF)
% Donat una llista de variables booleanes,
% -> el segon parametre sera la CNF que codifica que com a molt una sigui certa.
comamoltUn(L,CNF):- nega(L,NL), parelles(NL,CNF).

% AUX
% nega(L,N)
% Donat una llista de variables booleanes,
% -> el segon parametre sera la llista de varbiables booleanes negades
nega([],[]).
nega([X|Xs],N):- nega(Xs,R), XN is -X, append([XN],R,N), !.

% AUX
parelles([],[]).
parelles([H|T],P) :- parelles(H,T,P).

parelles(A,[],[]) :- !.
parelles(A,[B],[[A,B]]) :- !.
parelles(A,[B|T],P) :-
    combina(A,[B|T],P2),
    parelles(B,T,P3),
    append(P2,P3,P).

% AUX
combina(A,[B],[[A,B]]) :- !.
combina(A,[B|T],C) :- combina(A,T,C2), append([[A,B]],C2,C).

%%%%%%%%%%%%%%%%%%%
% exactamentUn(L,CNF)
% Donat una llista de variables booleanes,
% -> el segon parametre sera la CNF que codifica que exactament una sigui certa.
exactamentUn(L,CNF):- comaminimUn(L, S1), comamoltUn(L,S2), append(S1,S2,CNF).

%%%%%%%%%%%%%%%%%%%%%%%%%%%
% fesTauler(+N,+PI,+PP,V,I)
% Donat una dimensio de tauler N, unes posicions inicials PI i
% unes prohibides PP
% -> V sera la llista de llistes variables necessaries per codificar el tauler
% -> I sera la CNF codificant posicions inicials i prohibides

fesTauler(N,PI,PP,V,I):- X is N*N, llista(1,X,Y), trosseja(Y,N,V), fixa(PI,N,S1), prohibeix(PP,N,S2), append(S1,S2,I).

% AUX
% llista(I,F,L)
% Donat un inici i un fi
% -> el tercer parametre sera una llista de numeros d'inici a fi
llista(I,F,[]):- X is F-I, X < 0, !.
llista(I,F,L):- X is I+1, llista(X,F,S), append([I],S,L).

% AUX
% trosseja(L,N,LL)
% Donada una llista (L) i el numero de trossos que en volem (N)
% -> LL sera la llista de N llistes de L amb la mateixa mida
% (S'assumeix que la llargada de L i N ho fan possible)
trosseja([],_,[]).
trosseja(L,N,LL) :- length(L,Z), R is div(Z,N), length(X,R), trossejaN(L,R,LL), !.

% AUX
% trossejaN(L,N,LL)
% Donada una llista (L) i el numero d'elements de cada llista (N)
% -> LL sera la llista de llistes amb mida N de L amb la mateixa mida
trossejaN([],_,[]).
trossejaN(L,N,[X|Xs]):- length(X,N), append(X,Y,L), trossejaN(Y,N,Xs).

% AUX
% fixa(PI,N,F)
% donada una llista de tuples de posicions PI i una mida de tauler N
% -> F es la CNF fixant les corresponents variables de posicions a certa
fixa([],_,[]).
fixa([(X,Y)|Xs],N,F):- P is (X-1)*N+Y, fixa(Xs,N,R), append([[P]],R,F).

% AUX
% prohibeix(PP,N,P)
% donada una llista de tuples de posicions prohibides PP i una mida  tauler N
% -> P es la CNF posant les corresponents variables de posicions a fals
prohibeix([],_,[]).
prohibeix([(X,Y)|Xs],N,F):- P is -((X-1)*N+Y), prohibeix(Xs,N,R), append([[P]],R,F).

%%%%%%%%%%%%%%%%%%%%%%%
% noAmenacesFiles(+V,F)
% donada la matriu de variables,
% -> F sera la CNF que codifiqui que no s'amenecen les reines de les mateixes files
noAmenacesFiles([],[]).
noAmenacesFiles([X|Xs], F):- comamoltUn(X,S1), noAmenacesFiles(Xs,S2), append(S1, S2, F).

%%%%%%%%%%%%%%%%%%%%%%%%%%
% noAmenacesColumnes(+V,C)
% donada la matriu de variables,
% -> C sera la CNF que codifiqui que no s'amenecen les reines de les mateixes columnes
noAmenacesColumnes([],[]).
noAmenacesColumnes(X, C):- transpose(X,Y), noAmenacesFiles(Y,C).

% AUX
transpose([], []).
transpose([F|Fs], Ts):- transpose(F, [F|Fs], Ts).

% AUX
transpose([], _, []).
transpose([_|Rs], Ms, [Ts|Tss]):- lists_firsts_rests(Ms, Ts, Ms1), transpose(Rs, Ms1, Tss).

% AUX
lists_firsts_rests([], [], []).
lists_firsts_rests([[F|Os]|Rest],[F|Fs],[Os|Oss]):- lists_firsts_rests(Rest, Fs, Oss).

%%%%%%%%%%%%%%%%%%%%%%%%%%%
% noAmenacesDiagonals(+N,C)
% donada la mida del tauler,
% -> D sera la CNF que codifiqui que no s'amenecen les reines de les mateixes diagonals
noAmenacesDiagonals(N,D):- diagonals(N,L), llistesDiagonalsAVars(L,N,V), noAmenacesFiles(V,D).

% Genera les llistes de diagonals d'una matriu NxN. Cada diagonal es una llista de coordenades.
diagonals(N,L):- diagonalsIn(1,N,L1), diagonals2In(1,N,L2), append(L1,L2,L).

% diagonalsIn(D,N,L)
% Generem les diagonals dalt-dreta a baix-esquerra, D es el numero de
% diagonals, N la mida del tauler i L seran les diagonals generades
% Exemple:
% ?- diagonalsIn(1,3,L).
% L = [[(1,1)],[(1,2),(2,1)],[(1,3),(2,2),(3,1)],[(2,3),(3,2)],[(3,3)]]
% Evidentment les diagonals amb una sola coordenada les ignorarem...
diagonalsIn(D,N,[]):-D is 2*N,!.
diagonalsIn(D,N,[L1|L]):- D=<N,fesDiagonal(1,D,L1), D1 is D+1, diagonalsIn(D1,N,L).
diagonalsIn(D,N,[L1|L]):- D>N, F is D-N+1,fesDiagonalReves(F,N,N,L1), D1 is D+1, diagonalsIn(D1,N,L).

fesDiagonal(F,1,[(F,1)]):- !.
fesDiagonal(F,C,[(F,C)|R]):- F1 is F+1, C1 is C-1, fesDiagonal(F1,C1,R).

% quan la fila es N parem
fesDiagonalReves(N,C,N,[(N,C)]):-!.
fesDiagonalReves(F,C,N,[(F,C)|R]):-F1 is F+1, C1 is C-1, fesDiagonalReves(F1,C1,N,R).

% diagonals2In(D,N,L)
% Generem les diagonals baix-dreta a dalt-esquerra
% Exemple
% ?- diagonals2In(1,3,L).
% L = [[(3,1)],[(3,2),(2,1)],[(3,3),(2,2),(1,1)],[(2,3),(1,2)],[(1,3)]]
diagonals2In(D,N,[]):-D is 2*N,!.
diagonals2In(D,N,[L1|L]):- D<N,fesDiagonal2(N,D,L1), D1 is D+1, diagonals2In(D1,N,L). % començem pel final
diagonals2In(D,N,L):- D>=N, F is D-N+1,fesDiagonalReves2(F,N,L1), D1 is D+1, diagonals2In(D1,N,L2), append(L2, [L1], L). % treiem paràmetre

fesDiagonal2(F,1,[(F,1)]):- !.
fesDiagonal2(F,C,[(F,C)|R]):- F1 is F-1, C1 is C-1, fesDiagonal2(F1,C1,R). % decrementem fila i columna

% quan la fila es 1 parem, no necesitem paràmetre N
fesDiagonalReves2(1,C,[(1,C)]):- !.
fesDiagonalReves2(F,C,[(F,C)|R]):- F1 is F-1, C1 is C-1, fesDiagonalReves2(F1,C1,R). % decrementem fila i columna

% Passa una llista de coordenades  de tauler NxN a variables corresponents.
coordenadesAVars([],_,[]).
coordenadesAVars([(F,C)|R],N,[V|RV]):- V is (F-1)*N+C, coordenadesAVars(R,N,RV).

% Passa una llista de diagonals a llistes de llistes de variables
llistesDiagonalsAVars([],N,[]).
llistesDiagonalsAVars([P|Ps],N,[S1|S2]):- coordenadesAVars(P,N,S1),llistesDiagonalsAVars(Ps,N,S2).

%%%%%%%%%%%%%%%%%%%%%
% minimNReines(+V,FN)
% donada la matriu de variables (inicialment d'un tauler NxN),
% -> FN sera la CNF que codifiqui que hi ha d'haver com a minim N reines al tauler
minimNReines([],[]).
minimNReines([V|Vs],FN):- comaminimUn(V,S1), minimNReines(Vs,S2), append(S1,S2,FN).


prova(A):-append([1,2],[],A).
prova(A):-append([1,3],[],A).
prova(A):-append([1,4],[],A).

%%%%%%%%%
% resol()
% Ens demana els parametres del tauler i l'estat inicial,
% codifica les restriccions del problema i en fa una formula
% que la enviem a resoldre amb el SAT solver
% i si te solucio en mostrem el tauler

entrada(N,I,P):-
    write('Mida del tauler'), nl, read(N),
    write('Posicions per fixar'), nl, read(I),
    write('Posicions per prohibir'), nl, read(P).

resol(N,I,P):-
    entrada(N,I,P),
    fesTauler(N,I,P,V,Ini),
    minimNReines(V,FN),
    noAmenacesFiles(V,CNFfiles),
    noAmenacesColumnes(V,CNFcolumnes),
    noAmenacesDiagonals(N,CNFdiagonals),
    append(Ini,FN,CNF1),
    append(CNF1, CNFfiles,CNF2),
    append(CNF2, CNFcolumnes,CNF3),
    append(CNF3, CNFdiagonals,CNF),
    sat(CNF,[],M),
    treuNegatius(M,MP),
    sort(MP,MPS),
    write(MPS).

treuNegatius([],[]).
treuNegatius([V|Vs],S):- V < 0, treuNegatius(Vs,S),!.
treuNegatius([V|Vs],[V|S]):- V > 0, treuNegatius(Vs, S),!.

%%%%%%%%%%%%%%%%%%%
% mostraTauler(N,M)
% donat una mida de tauler N i una llista de numeros d'1 a N*N,
% mostra el tauler posant una Q a cada posicio recorrent per files
% d'equerra a dreta.
% Per exemple:
% | ?- mostraTauler(3,[1,5,8,9...]).
% -------
% |Q| | |
% -------
% | |Q| |
% -------
% | |Q|Q|
% -------
% Fixeu-vos que li passarem els literals positius del model de la nostra
% formula.
% ...
