%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% SIST. REPR. CONHECIMENTO E RACIOCINIO - MiEI/3
% Programacao em logica estendida e conhecimento imperfeito
% Trabalho prático nº 2
%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% SICStus PROLOG: Declaracoes iniciais
:- set_prolog_flag( discontiguous_warnings,off ).
:- set_prolog_flag( single_var_warnings,off ).
:- set_prolog_flag( unknown,fail ).
:- op( 900,xfy,'::' ).
:- dynamic data/3.
:- dynamic excecao/1.
:- dynamic utente/4.
:- dynamic nome/1.
:- dynamic descricao/1.
:- dynamic cidade/1.
:- dynamic morada/1.
:- dynamic instituicao/1.
:- dynamic cuiprest/4.
:- dynamic amed/4.
:- dynamic impreciso/3.
:- dynamic nulo/1.


%--------------------------------------------------------------
% Extensao do predicado utente: #IdUt, Nome, Idade, Morada -> {V,F}
utente(u1 , nome('joao miguel') , 30 , morada('rua de barros')).
utente(u2 , nome('bruno machado') , 20 , morada('rua de santa apolonia')).
utente(u3 , nome('carlos silva') , 20 , morada('rua do souto')).
utente(u4 , nome('paulo guedes') , 20 , morada('rua penedo da forca')).
utente(u5 , nome('goncalo moreira') , 20 , morada('rua padre francisco babo')).

%----------------------------------------------------------------------
% Invariante Referencial: nao admitir mais do que 1 utente
%                         com o mesmo id
+utente(U,N,I,M) :: (
                      solucoes( U , utente( U , _ , _ , _ ) , S ),
                      comprimento( S , T ),
                      T =< 1
                    ).

%
+excecao(P) :: (
                solucoes(P,excecao(P), S),
                comprimento(S,R),
                R=<1
               ).

%----------------------------------------------------------------------
% Invariante Referencial: nao admitir remocao de utentes que
%                         estejam ligados a um ato medico
-utente(U,N,I,M) :: (
                      solucoes( U, amed( D, U, S, P), S),
                      comprimento(S,T),
                      T==0
                    ).

%----------------------------------------------------------------------
%Invariante Estrutural: impõe o pressuposto do mundo fechado
-utente(U,N,I,M) :- nao( utente( U, N, I, M ) ),
                    nao( excecao( utente( U, N, I, M ) ) ).


%--------------------------------------------------------
% Entensao do predicado incerto,
% incerto: Utente, [Posicao Incerto Desejado], -> {V,F}

incerto(utente(U,N,I,M), [2]) :- nao(utente(U,_,_,_)),
                                 evolucao(excecao(utente(U,_,I,M))).
incerto(utente(U,N,I,M), [3]) :- nao(utente(U,_,_,_)),
                                 evolucao(excecao(utente(U,N,_,M))).
incerto(utente(U,N,I,M), [4]) :- nao(utente(U,_,_,_)),
                                 evolucao(excecao(utente(U,N,I,_))).
incerto(utente(U,N,I,M), [2,3]) :- nao(utente(U,_,_,_)),
                                   evolucao(excecao(utente(U,_,_,M))).
incerto(utente(U,N,I,M), [3,4]) :- nao(utente(U,_,_,_)),
                                   evolucao(excecao(utente(U,N,_,_))).

%--------------------------------------------------------
% Entensao do predicado impreciso,
% impreciso: Utente, Condiçao(opcional), Condiçao(opcional) -> {V,F}

impreciso(utente(U,N,I,M), I>R) :- nao(utente(U,_,_,_)),
                                   evolucao((excecao(utente(U,N,X,M)) :- X>R)).
impreciso(utente(U,N,I,M), I<R) :- nao(utente(U,_,_,_)),
                                   evolucao((excecao(utente(U,N,X,M)) :- X<R)).
impreciso(utente(U,N,I,M), I>R1, I<R2) :- nao(utente(U,_,_,_)),
                                          evolucao((excecao(utente(U,N,X,M)) :- X>R1, X<R2)).
impreciso(utente(U,N,I,M)) :- nao(utente(U,_,_,_)),
                              evolucao(excecao(utente(U,N,I,M))).


%--------------------------------------------------------
% Entensao do predicado excecao,
% excecao: Utente-> {V,F}

excecao(utente(U,N,I,M)) :- utente(U,N,idade,M).
excecao(utente(U,N,I,M)) :- utente(U,N,I,morada).
excecao(utente(U,N,I,M)) :- utente(U,nome,I,M).
excecao(utente(U,N,I,M)) :- utente(U,nome,idade,M).
excecao(utente(U,N,I,M)) :- utente(U,N,idade,morada).
excecao(utente(U,N,I,M)) :- utente(U,nome,I,morada).
excecao(utente(U,N,I,M)) :- utente(U,nome,idade,morada).

%--------------------------------------------------------
% Entensao do predicado nulo,
% nulo: Parâmetro -> {V,F}

nulo(idade).
nulo(morada).
nulo(nome).

%--------------------------------------------------------
% Entensao do predicado interdito,
% interdito: Utente, [Posicao Interdito Desejado] -> {V,F}

interdito(utente(U,N,I,M), [3]) :- nao(utente(U,_,_,_)),
                                   evolucao(utente(U,N,idade,M)).
interdito(utente(U,N,I,M), [2]) :- nao(utente(U,_,_,_)),
                                   evolucao(utente(U,nome,I,M)).
interdito(utente(U,N,I,M), [4]) :- nao(utente(U,_,_,_)),
                                   evolucao(utente(U,N,I,morada)).
interdito(utente(U,N,I,M), [3, 4]) :- nao(utente(U,_,_,_)),
                                      evolucao(utente(U,N,idade,morada)).
interdito(utente(U,N,I,M), [2, 4]) :- nao(utente(U,_,_,_)),
                                      evolucao(utente(U,nome,I,morada)).
interdito(utente(U,N,I,M), [2, 3]) :- nao(utente(U,_,_,_)),
                                      evolucao(utente(U,nome,idade,M)).
interdito(utente(U,N,I,M), [2,3, 4]) :- nao(utente(U,_,_,_)),
                                      evolucao(utente(U,nome,idade,morada)).



%--------------------------------------------------------
% Entensao do predicado cuidado prestado,
% cuiprest: #IdServ, Descrição, Instituição, Cidade -> {V,F}
cuiprest( c1 ,
          descricao('remocao de sinal nas costas') ,
          instituicao('sao joao') ,
          cidade('porto')).
cuiprest( c2 ,
          descricao('curativo pos operatorio') ,
          instituicao('unidade local de saude') ,
          cidade('matosinhos')).
cuiprest( c3 ,
          descricao('injecao') ,
          instituicao('sao joao') ,
          cidade('porto')).
cuiprest( c4 ,
          descricao('eletrocardiograma') ,
          instituicao('hospital beatriz angelo') ,
          cidade('loures')).
cuiprest( c5 ,
          descricao('analise clinica') ,
          instituicao('centro hospitalar') ,
          cidade('braga')).
% Invariante Referencial: nao admitir mais do que 1 cuidado prestado
%                         com o mesmo id
+cuiprest(U,D,I,C) :: (
                      solucoes( U , cuiprest( U , _ , _ , _ ) , S ),
                      comprimento( S , T ),
                      T =< 1
                    ).
% Invariante Referencial: nao admitir a remocao de um cuidado prestado
%                         que esteja ligado a um ato medico
-cuiprest(U,D,I,C) :: (
                      solucoes( S , amed( _ , _ , U , _ ) , R ),
                      comprimento( R , T ),
                      T == 0
                    ).

%--------------------------------------------------------
%Invariante Estrutural: impõe o pressuposto do mundo fechado
-cuiprest( Id, D, I, C ) :- nao( cuiprest( Id, D, I, C ) ),
                            nao( excecao( cuiprest( Id, D, I, C ) ) ).


%--------------------------------------------------------
% Entensao do predicado incerto,
% incerto: cuidadoPrestado, [Posicao Incerto Desejado] -> {V,F}

incerto(cuiprest(Id,D,I,C), [2]) :- nao(cuiprest(Id,_,_,_)),
                                    evolucao(excecao(cuiprest(Id,_,I,C))).
incerto(cuiprest(Id,D,I,C), [3]) :- nao(cuiprest(Id,_,_,_)),
                                    evolucao(excecao(cuiprest(Id,D,_,C))).
incerto(cuiprest(Id,D,I,C), [4]) :- nao(cuiprest(Id,_,_,_)),
                                    evolucao(excecao(cuiprest(Id,D,I,_))).
incerto(cuiprest(Id,D,I,C), [2,3]) :- nao(cuiprest(Id,_,_,_)),
                                      evolucao(excecao(cuiprest(Id,_,_,C))).
incerto(cuiprest(Id,D,I,C), [2,4]) :- nao(cuiprest(Id,_,_,_)),
                                      evolucao(excecao(cuiprest(Id,_,I,_))).
incerto(cuiprest(Id,D,I,C), [3,4]) :- nao(cuiprest(Id,_,_,_)),
                                      evolucao(excecao(cuiprest(Id,D,_,_))).
incerto(cuiprest(Id,D,I,C), [2,3,4]) :- nao(cuiprest(Id,_,_,_)),
                                      evolucao(excecao(cuiprest(Id,D,_,_))).

%--------------------------------------------------------
% Entensao do predicado impreciso,
% impreciso: cuidadoPrestado -> {V,F}

impreciso(cuiprest(Id,D,I,C)) :- nao(cuiprest(Id,_,_,_)),
                                 evolucao(excecao(cuiprest(Id,D,I,C))).

%--------------------------------------------------------
% Entensao do predicado excecao,
% excecao: cuidadoPrestado -> {V,F}

excecao(cuiprest(Id,D,I,C)) :- cuiprest(Id,D,instituicao,C).
excecao(cuiprest(Id,D,I,C)) :- cuiprest(Id,descricao,I,C).
excecao(cuiprest(Id,D,I,C)) :- cuiprest(Id,D,I,cidade).
excecao(cuiprest(Id,D,I,C)) :- cuiprest(Id,descricao,instituicao,C).
excecao(cuiprest(Id,D,I,C)) :- cuiprest(Id,descricao,I,cidade).
excecao(cuiprest(Id,D,I,C)) :- cuiprest(Id,D,instituicao,cidade).
excecao(cuiprest(Id,D,I,C)) :- cuiprest(Id,descricao,instituicao,cidade).

%--------------------------------------------------------
% Entensao do predicado nulo,
% nulo: Parâmetro -> {V,F}

nulo(descricao).
nulo(instituicao).
nulo(cidade).

%--------------------------------------------------------
% Entensao do predicado interdito,
% interdito: cuidadoPrestado, [Posicao Interdito Desejado] -> {V,F}

interdito(cuiprest(Id,D,I,C), [2]) :- nao(cuiprest(Id,_,_,_)),
                                      evolucao(cuiprest(Id,descricao,I,C)).
interdito(cuiprest(Id,D,I,C), [3]) :- nao(cuiprest(Id,_,_,_)),
                                      evolucao(cuiprest(Id,D,instituicao,C)).
interdito(cuiprest(Id,D,I,C), [4]) :- nao(cuiprest(Id,_,_,_)),
                                      evolucao(cuiprest(Id,D,I,cidade)).
interdito(cuiprest(Id,D,I,C), [2,3]) :- nao(cuiprest(Id,_,_,_)),
                                        evolucao(cuiprest(Id,descricao,instituicao,C)).
interdito(cuiprest(Id,D,I,C), [2,4]) :- nao(cuiprest(Id,_,_,_)),
                                        evolucao(cuiprest(Id,descricao,I,cidade)).
interdito(cuiprest(Id,D,I,C), [3,4]) :- nao(cuiprest(Id,_,_,_)),
                                        evolucao(cuiprest(Id,D,instituicao,cidade)).
interdito(cuiprest(Id,D,I,C), [2,3,4]) :- nao(cuiprest(Id,_,_,_)),
                                          evolucao(cuiprest(Id,descricao,instituicao,cidade)).


%-----------------------------------------------------------------------
% Entensao do predicado ato médico: Data, #IdUt, #IdServ, Custo -> {V,F}
amed(data(21, 02, 2017) , u1 , c4 , 100).
amed(data(21, 02, 2017) , u1 , c2 , 100).
amed(data(12, 01, 2017) , u2 , c5 , 10).
amed(data(30, 01, 2017) , u3 , c3 , 5).
amed(data(24, 02, 2017) , u4 , c1 , 20).
amed(data(24, 02, 2017) , u3 , c1 , 20).
amed(data(15, 03, 2017) , u5 , c2 , 45).

%------------------------------------------------------------------------
% Invariante Referencial: nao admitir mais do que 1 ato medico
%                         com a mesma data e com o mesmo id de utente
%                         e cuidado prestado

+amed(D,U,S,P) :: (
                    solucoes((D, U, S), amed(D, U, S, _), L),
                    comprimento(L, N),
                    N =< 1
                  ).

%------------------------------------------------------------------------
%Invariante Estrutural: impõe o pressuposto do mundo fechado
-amed(D,U,S,P) :- nao(amed(D,U,S,P)),
                  nao(excecao(amed(D,U,S,P))).


%--------------------------------------------------------
% Entensao do predicado incerto,
% incerto: atoMedico, [Posicao Incerto Desejado] -> {V,F}

incerto(amed(D,U,S,P), [1]) :- evolucao(excecao(amed(_,U,S,P))).
incerto(amed(D,U,S,P), [3]) :- evolucao(excecao(amed(D,U,_,P))).
incerto(amed(D,U,S,P), [4]) :- nao(amed(D,U,S,_)),
                               evolucao(excecao(amed(D,U,S,_))).
incerto(amed(D,U,S,P), [1,3]) :- evolucao(excecao(amed(_,U,_,P))).
incerto(amed(D,U,S,P), [1,4]) :- evolucao(excecao(amed(_,U,S,_))).
incerto(amed(D,U,S,P), [3,4]) :- evolucao(excecao(amed(D,U,_,_))).
incerto(amed(D,U,S,P), [1,3,4]) :- evolucao(excecao(amed(_,U,_,_))).

%--------------------------------------------------------
% Entensao do predicado impreciso,
% impreciso: atoMedico -> {V,F}

impreciso(amed(D,U,S,P)) :- nao(amed(D,U,S,_)),
                            evolucao(excecao(amed(D,U,S,P))).

%--------------------------------------------------------
% Entensao do predicado excecao,
% excecao: atoMedico -> {V,F}

excecao(amed(D,U,S,P)) :- amed(D,U,S,preco).

%--------------------------------------------------------
% Entensao do predicado nulo,
% nulo: Parâmetro -> {V,F}

nulo(preco).

%--------------------------------------------------------
% Entensao do predicado interdito,
% interdito: atoMedico, [Posicao Interdito Desejado] -> {V,F}

interdito(amed(D,U,S,C), [4]) :- nao(amed(D,U,S,_)),
                                 evolucao(amed(D,U,S,preco)).


%------------------------------------- - - - - - - - - - - - - - - - - - -
%% Extensao do meta-predicado mydemo: Questao, e, Questao,Resposta -> {V,F,D}


%---------CONJUÇÃO com "e" ------

%verdadeiro, verdadeiro
mydemo( Questao1,e,Questao2,verdadeiro ) :-
              Questao1,
              Questao2.

%verdadeiro, desconhecido
mydemo( Questao1,e,Questao2, desconhecido ) :-
              Questao1,
              nao(Questao2),
              nao(-Questao2).

%desconhecido, verdadeiro
mydemo( Questao1,e,Questao2, desconhecido ) :-
              nao(Questao1),
              nao(-Questao1),
              Questao2.

%verdadeiro, falso
mydemo( Questao1,e,Questao2, falso ) :-
              Questao1,
              -Questao2.

%falso, verdadeiro
mydemo( Questao1,e,Questao2, falso ) :-
              -Questao1,
              Questao2.

%falso, desconhecido
mydemo( Questao1,e,Questao2, falso ) :-
              -Questao1,
              nao(Questao2),
              nao(-Questao2).

%falso, falso
mydemo( Questao1,e,Questao2, falso ) :-
              -Questao1,
              -Questao2.

%desconhecido, falso
mydemo( Questao1,e,Questao2, desconhecido ) :-
              nao(Questao1),
              nao(-Questao1),
              -Questao2.

%desconhecido, desconhecido
mydemo( Questao1,e,Questao2, desconhecido ) :-
              nao(Questao1),
              nao(-Questao1),
              nao(Questao2),
              nao(-Questao2).



%---------DIJUNÇAO com "v" ------

%verdadeiro, verdadeiro
mydemo( Questao1,v,Questao2, verdadeiro ) :-
              Questao1,
              Questao2.

%falso, falso
mydemo( Questao1,v,Questao2, falso ) :-
              -Questao1,
              -Questao2.

%desconhecido, desconhecido
mydemo( Questao1,v,Questao2, desconhecido ) :-
              nao(Questao1),
              nao(-Questao1),
              nao(Questao2),
              nao(-Questao2).

%verdadeiro, falso
mydemo( Questao1,v,Questao2, verdadeiro ) :-
              Questao1,
              -Questao2.

%falso, verdadeiro
mydemo( Questao1,v,Questao2, verdadeiro ) :-
              -Questao1,
              Questao2.

%desconhecido, falso
mydemo( Questao1,v,Questao2, desconhecido ) :-
              nao(Questao1),
              nao(-Questao1),
              -Questao2.

%falso, desconhecido
mydemo( Questao1,v,Questao2, desconhecido ) :-
              -Questao1,
              nao(Questao2),
              nao(-Questao2).

%desconhecido, verdadeiro
mydemo( Questao1,v,Questao2, verdadeiro ) :-
              nao(Questao1),
              nao(-Questao1),
              Questao2.

%verdadeiro, desconhecido
mydemo( Questao1,v,Questao2, verdadeiro ) :-
              Questao1,
              nao(Questao2),
              nao(-Questao2).


%------------------------------------- - - - - - - - - - - - - - - - - - -
%% Extensao do meta-predicado demoC: Valor, Valor, Resposta -> {V,F,D}

demoC(verdadeiro,verdadeiro,verdadeiro).
demoC(verdadeiro,falso,falso).
demoC(verdadeiro,desconhecido,desconhecido).
demoC(falso,falso, falso).
demoC(falso,verdadeiro,falso).
demoC(falso,desconhecido,desconhecido).
demoC(desconhecido,desconhecido,desconhecido).
demoC(desconhecido,verdadeiro,desconhecido).
demoC(desconhecido,falso,desconhecido).

%------------------------------------- - - - - - - - - - - - - - - - - - -
%% Extensao do meta-predicado demoD: Valor, Valor, Resposta -> {V,F,D}

demoD(verdadeiro,verdadeiro,verdadeiro).
demoD(verdadeiro,falso,verdadeiro).
demoD(verdadeiro,desconhecido,verdadeiro).
demoD(falso,falso, falso).
demoD(falso,verdadeiro,verdadeiro).
demoD(falso,desconhecido,falso).
demoD(desconhecido,desconhecido,desconhecido).
demoD(desconhecido,verdadeiro,verdadeiro).
demoD(desconhecido,falso,falso).

%------------------------------------- - - - - - - - - - - - - - - - - - -
%% Extensao do meta-predicado demoLista: [Questao], Resposta -> {V,F,D}

demoLista([Q2],R).
demoLista([Q1,e,Q2|T],R) :-
              mydemo(Q1,e,Q2,R1),
              demoLista([Q2|T],R2),
              demoC(R1,R2,R).

demoLista([Q1,v,Q2|T],R) :-
              mydemo(Q1,v,Q2,R1),
              demoLista([Q2|T],R2),
              demoD(R1,R2,R).



%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do meta-predicado demo: Questao,Resposta -> {V,F}
demo( Questao,verdadeiro ) :-
              Questao.
demo( Questao, falso ) :-
              -Questao.
demo( Questao,desconhecido ) :-
              nao( Questao ),
              nao( -Questao ).

%--------------------------------------------------------------
% Extensao do meta-predicado nao: Questao {V,F}
nao(Q) :- Q, !, fail.
nao(Q).


%--------------------------------------------------------------
% Extensao do meta-predicado solucoes: F, Q, S -> {V,F}
solucoes(F, Q, S) :- findall(F, Q, S).


%--------------------------------------------------------------
% Extensao do meta-predicado comprimento: L, N -> {V,F}
comprimento([], 0).
comprimento([H | T], N) :-
                      comprimento(T, R),
                      N is R + 1.


%--------------------------------------------------------------
% Extensao do meta-predicado testar: Li -> {V,F}
testar([]).
testar([H | T]) :- H,
                  testar(T).


%--------------------------------------------------------------
% Extensao do meta-predicado inserir: F -> {V,F}
inserir(F) :- assert(F).
inserir(F) :- retract(F), !, fail.


%--------------------------------------------------------------
% Extensao do meta-predicado evolucao: F -> {V,F}
evolucao(F) :-  solucoes(I, +F::I, Li),
                inserir(F),
                testar(Li).


%--------------------------------------------------------------
% Extensao do predicado morada: Morada -> {V,F}
-morada( M ) :- nao( morada( M ) ),
                nao( excecao( morada( M ) ) ).
          morada('rua de barros').
          morada('rua de santa apolonia').
          morada('rua do souto').
          morada('rua penedo da forca').
          morada('rua padre francisco babo').
% Invariante Estrutural:  nao permitir a insercao de conhecimento
%                         repetido
+morada(M) :: (
              solucoes( M, morada(M), S),
              comprimento(S, N),
              N =< 1
              ).
% Invariante Estrutural:  nao permitir a remocao de conhecimento
-morada(M) :: fail.


%--------------------------------------------------------------
% Extensao do predicado nome: Nome -> {V,F}
-nome( N ) :- nao( nome( N ) ),
              nao( excecao( nome( N ) ) ).
nome('joao miguel').
nome('bruno machado').
nome('carlos silva').
nome('paulo guedes').
nome('goncalo moreira').
nome('rui manel').
% Invariante Estrutural:  nao permitir a insercao de conhecimento
%                         repetido
+nome(N) :: (
            solucoes( N, nome(N), S),
            comprimento(S,T),
            T =< 1
            ).
% Invariante Estrutural:  nao permitir a remocao de conhecimento
-nome(N) :: fail  .


%--------------------------------------------------------------
% Extensão do predicado Utente que permite a evolucao
% do conhecimento de utentes
registarUtente(U,N,I,M):- evolucao(utente(U,N,I,M)),
                          N,
                          M,
                          involucaoL(excecao(utente(U,_,_,_))).
registarUtente(U,N,I,M):- evolucao(utente(U,N,I,M)),
                          N,
                          evolucao(M),
                          involucaoL(excecao(utente(U,_,_,_))).
registarUtente(U,N,I,M):- evolucao(utente(U,N,I,M)),
                          evolucao(N),
                          M,
                          involucaoL(excecao(utente(U,_,_,_))).
registarUtente(U,N,I,M):- evolucao(utente(U,N,I,M)),
                          evolucao(N),
                          evolucao(M),
                          involucaoL(excecao(utente(U,_,_,_))).


%--------------------------------------------------------------
% Extensão do predicado removerUtente que permite a regressao
% do conhecimento de utentes
removerUtente(U,N,I,M):- involucao(utente(U,N,I,M)).


%------------------------------------------------------
% Extensao do predicado descricao: Descricao -> {V,F}
-descricao( D ) :- nao( descricao( D ) ),
                   nao( excecao( descricao( D ) ) ).
descricao('remocao de sinal nas costas').
descricao('curativo pos operatorio').
descricao('injecao').
descricao('eletrocardiograma').
descricao('analise clinica').
% Invariante Estrutural:  nao permitir a insercao de conhecimento
%                         repetido
+descricao(D) :: (
                  solucoes( D , descricao(D) , S ),
                  comprimento( S , N ),
                  N =< 1
                 ).
% Invariante Estrutural:  nao permitir a remocao de conhecimento
-descricao(D) :: fail.


%--------------------------------------------------------
% Extensao do predicado instituicao: Instituicao -> {V,F}
-instituicao( I ) :- nao( instituicao( I ) ),
                     nao( excecao( instituicao( I ) ) ).
instituicao('sao joao').
instituicao('unidade local de saude').
instituicao('hospital beatriz angelo').
instituicao('centro hospitalar').
% Invariante Estrutural:  nao permitir a insercao de conhecimento
%                         repetido
+instituicao(I) :: (
                  solucoes( I, instituicao(I), S),
                  comprimento(S, N),
                  N =< 1
                  ).
% Invariante Estrutural:  nao permitir a remocao de conhecimento
-instituicao(I) :: fail.


%--------------------------------------------------------
% Extensao do precicado cidade: Cidade -> {V,F}
-cidade( C ) :- nao( cidade( C ) ),
                nao( excecao( cidade( C ) ) ).
  cidade('porto').
  cidade('matosinhos').
  cidade('loures').
  cidade('braga').
  % Invariante Estrutural:  nao permitir a insercao de conhecimento
  %                         repetido
  +cidade(D) :: (
                solucoes( D, cidade(D), S),
                comprimento(S, N),
                N =< 1
                ).
  % Invariante Estrutural:  nao permitir a remocao de conhecimento
  -cidade(D) :: fail.


%--------------------------------------------------------------
% Extensão do predicado registarCuiPrest que permite a evolucao
% do conhecimento de cuidados prestados
registarCuiPrest(U,D,I,C):- evolucao(cuiprest(U,D,I,C)),
                            D,
                            I,
                            C,
                            involucaoL(excecao(cuiprest(U,_,_,_))).
registarCuiPrest(U,D,I,C):- evolucao(cuiprest(U,D,I,C)),
                            evolucao(D),
                            evolucao(I),
                            evolucao(C),
                            involucaoL(excecao(cuiprest(U,_,_,_))).
registarCuiPrest(U,D,I,C):- evolucao(cuiprest(U,D,I,C)),
                            evolucao(D),
                            I,
                            C,
                            involucaoL(excecao(cuiprest(U,_,_,_))).
registarCuiPrest(U,D,I,C):- evolucao(cuiprest(U,D,I,C)),
                            D,
                            evolucao(I),
                            C,
                            involucaoL(excecao(cuiprest(U,_,_,_))).
registarCuiPrest(U,D,I,C):- evolucao(cuiprest(U,D,I,C)),
                            D,
                            I,
                            evolucao(C),
                            involucaoL(excecao(cuiprest(U,_,_,_))).
registarCuiPrest(U,D,I,C):- evolucao(cuiprest(U,D,I,C)),
                            evolucao(D),
                            evolucao(I),
                            C,
                            involucaoL(excecao(cuiprest(U,_,_,_))).
registarCuiPrest(U,D,I,C):- evolucao(cuiprest(U,D,I,C)),
                            evolucao(D),
                            I,
                            evolucao(C),
                            involucaoL(excecao(cuiprest(U,_,_,_))).
registarCuiPrest(U,D,I,C):- evolucao(cuiprest(U,D,I,C)),
                            D,
                            evolucao(I),
                            evolucao(C),
                            involucaoL(excecao(cuiprest(U,_,_,_))).


%--------------------------------------------------------------
% Extensão do predicado removerCuiPrest que permite a regressao
% do conhecimento de cuidados prestados
removerCuiPrest(U,D,I,C):- involucao(cuiprest(U,D,I,C)).


%-----------------------------------------------------------------------
% Extensao do predicado data: Dia, Mes, Ano -> {V,F}
data(21, 02, 2017).
data(12, 01, 2017).
data(30, 01, 2017).
data(24, 02, 2017).
data(15, 03, 2017).
% Invariante Estrutural:  nao permitir a insercao de conhecimento
%                         repetido
+data(D, M, A) :: (
solucoes( (D, M, A) , (data(D, M, A)) , S ),
comprimento(S, N),
N =< 1
).
% Invariante Estrutural:  nao permitir a remocao de conhecimento
-data(D, M, A) :: fail.


%----------------------------------------
% Extensão do predicado registarAmed que permite a evolucao
% do conhecimento de atos medicos

registaAMed(D,U,I,C) :- evolucao(D),
                        evolucao(amed(D,U,I,C)).
                        involucaoL(excecao(amed(D,U,I,_))).

registaAMed(D,U,I,C) :- evolucao(amed(D,U,I,C)).
                        involucaoL(excecao(amed(D,U,I,_))).


%----------------------------------------
% Extensão do predicado registarAmed que permite a regressao
% do conhecimento de atos medicos
removerAMed(D,I,I2,C) :- involucao(amed(U,D,I,C)).


%------------------------------------------------------------------
% Extensao do predico para concatenar duas listas,
% concatenar: Lista1, Lista2, e Listaf -> {V,F}
concatenar([], L2, L2).
concatenar([X|L1], L2, [X|L]) :- concatenar(L1, L2, L).


%------------------------------------------------------------------
% Extensao do predicado de filtrar por idade,
% filtraIdade Condicao,Idade,Lista -> {V,F}
filtraIdade( <, 0, [] ).
filtraIdade( <,I,N2 ) :- R is I-1,
                      filtraIdade( <, R, N ),
                      solucoes( No, utente( _, No, R, _ ), L1 ),
                      concatenar( L1, N, N2 ).
filtraIdade( >, 110, [] ).
filtraIdade( >, I, N2 ) :- R is I+1,
                      filtraIdade( >, R, N ),
                      solucoes( No, utente( _, No, R, _ ), L1 ),
                      concatenar( L1, N, N2 ).
filtraIdade( =, I, L ) :- solucoes( No, utente( _, No, I, _ ), L ).


%--------------------------------------------------------------
% Extensao do predicado para filtrar utentes por morada,
% filtraMorada: Morada, Lista -> {V,F}
filtraMorada(R,L) :- solucoes(No, utente(_, No, _, R), L).


%--------------------------------------------------------------
% Extensao do predicado para filtrar utentes por id,
% filtraId: ID, Lista -> {V,F}
filtraId(I,L) :- solucoes(No, utente(I, No , _ , _), L).


%--------------------------------------------------------------
% Extensao do predicado para filtrar utentes por cuidado prestado,
% filtrarCuiPrest: Descrição, Lista -> {V,F}
filtrarCuiPrest( D, L ) :-
                cuiprest(X,D,_,_),
                solucoes(N,amed(_,N,X,_),L1),
                utentesByID(L1,L).


%--------------------------------------------------------------
% Extensao do predicado para mostrar os utentes a partir de uma
% lista com ids de utentes
% utentesByID: Lista1, Lista -> {V,F}
utentesByID([],[]).
utentesByID([H|T],L) :-
          utente(H,N,_,_),
          utentesByID(T,R),
          concatenar([N],R,L).


%------------------------------------------------------------------
% Extensao do predicado para mostrar todas as instituicoes
% prestadores de cuidados de saude
% mostraInstituicoes: Lista -> {V,F}
mostraInstituicoes(L) :- solucoes( I ,cuiprest( _, _, instituicao(I), _) , L).


%------------------------------------------------------------------
% Extensao do predicado para mostrar os cuidados prestados
% numa determinada instituicao
% cuiPrestInst: Instituicao, Lista -> {V,F}
cuiPrestInst(I,L) :- solucoes( cuiprest( U, D, I, C), cuiprest( U, D, I, C), L).


% Extensao do predicado para mostrar os cuidados prestados
% numa determinada cidade
% cuiPrestCidade: Cidade, Lista -> {V,F}
cuiPrestCidade(C,L) :- solucoes(cuiprest(U,D,I,C),cuiprest(U,D,I,C), L).


%-----------------------------------------------------------------------------
% Extensao do predicado para mostrar os utentes a partir de uma
% lista com ids de utentes
% utent: Lista1, Lista -> {V,F}
utent([],[]).
utent([U|T],L) :- utent(T,L1),
                  solucoes(utente(U,N,I,M),utente(U,N,I,M),L2),
                  concatenar(L2,L1,L).


%--------------------------------------------------------------
% Extensao do predicado para, a partir dos ids de cuidados prestados
% obter os ids de utentes que estavam ligados a atos medicos,
% idU: Lista1, Lista -> {V,F}
idU([],[]).
idU([Is|T],L) :-  idU(T,L1),
                  solucoes(H,amed(_,H,Is,_),L2),
                  concatenar(L2,L1,L).


%--------------------------------------------------------------
% Extensao do predicado para,a partir de uma instiuicao,
% obter os ids de cuidados prestados,
% idSr: ID, Lista -> {V,F}
idSr(I,L) :- solucoes(U,cuiprest(U,_,I,_),L).


%--------------------------------------------------------------
% Extensao do predicado para, a partir de uma instiuicao,
% obter os utentes de uma instituicao,
% uInst: Instituicao, Lista -> {V,F}
uInst(I,L) :- idSr(I,A),
             idU(A,B),
             utent(B,L).


%-------------------------------------------------------------------------------
% Extensao do predicado para, a partir de um id de um serviço,
% obter os ids utentes que estao ligados ao ato medico daquele serviço,
% idUt: ID, Lista -> {V,F}
idUt(Is,L) :- solucoes(H,amed(_,H,Is,_),L).


%--------------------------------------------------------------
% Extensao do predicado para, a partir de um id de um serviço,
% obter os utentes que estao ligados ao ato medico daquele serviço,
% idUt: ID, Lista -> {V,F}
uServ(IdS,L) :- idUt(IdS,A),
                utent(A,L).


%----------------------------------------------------------------------------------
% Extensao do predicado para, a partir de um utente, obter a listagem
% de todos os atos medicos por este realizado.
% aMedUtent: Utente, Lista -> {V,F}
aMedUtent(utente(I,_,_,_),L) :-  solucoes(amed(A,I,B,C),amed(A,I,B,C),L).


%--------------------------------------------------------------
% Extensao do predicado, para obter a listagem de todos os
% ids de serviço prestados numa instituicao
% instServ: instituicao, Lista -> {V,F}
instServ(I,L) :- solucoes(U,cuiprest(U,_,I,_),L).


%--------------------------------------------------------------
% Extensao do predicado, para obter a listagem de todos os
% atos médicos correspondentes aos ids de servico presentes numa
% lista
% idServAmed: Lista (Ids servico), Lista (Atos medicos) -> {V,F}
idServAmed([],[]).
idServAmed([H|T],L):- idServAmed(T,L1),
                      solucoes(amed(U,N,H,M),amed(U,N,H,M),L2),
                      concatenar(L2,L1,L).


%--------------------------------------------------------------
% Extensao do predicado, para obter a listagem de todos os
% atos médicos correspondentes a uma instituicao
% amedInst: Instituicao, Lista -> {V,F}
amedInst(I,L) :- instServ(I,P),
                 idServAmed(P,L).


%--------------------------------------------------------------
% Extensao do predicado, para obter a listagem de todos os
% atos médicos correspondentes a um servico
% amedServ: Servico, Lista -> {V,F}
amedServ(I,L) :- solucoes(amed(D,I2,I,C),amed(D,I2,I,C),L).


%--------------------------------------------------------------
% Extensao do predicado, para obter a listagem de todos os
% servicos prestados por instituicao apartir da listagem de
% ids de cuidados prestados
% inSerAux: Lista (Ids cuidprest), Lista -> {V,F}
inSerAux([],[]).
inSerAux([H|T],L):- solucoes((I,H,D),cuiprest(H,D,I,_),L1),
                    inSerAux(T,L2),
                    concatenar(L1,L2,L).


%--------------------------------------------------------------
% Extensao do predicado, para obter a listagem de todos os
% servicos prestados por instituicao a um utente
% inSer: Utente, Lista -> {V,F}
inSer(U,L):-  solucoes(I,amed(_,U,I,_),L1),
              inSerAux(L1,L).


%--------------------------------------------------------------
% Extensao do predicado, para obter o custo total de todos
% os servicos efetuados numa data
% custoData: Data, Resultado -> {V,F}
custoData(D,R):-  solucoes(C,amed(D,I2,I,C),L),
                  soma(L,R).


%--------------------------------------------------------------
% Extensao do predicado, para obter o custo total de todos
% os servicos efetuados numa instituicao
% custoInstituicao: Instituicao, Resultado -> {V,F}
custoInstituicao(I,R):- solucoes(S,cuiprest(S,_,I,_),L),
                        custoInstituicaoAux(L,L2),
                        soma(L2,R).


%--------------------------------------------------------------
% Extensao do predicado, para obter uma lista com o custo
% de todos os servicos presentes numa outra lista de ids de cuidados
% prestados
% custoInstituicaoAux: Lista (ids cuidpres), Lista -> {V,F}
custoInstituicaoAux([],[]).
custoInstituicaoAux([H|T],L) :- solucoes(C,amed(D,I2,H,C),L2),
                                custoInstituicaoAux(T,L1),
                                concatenar(L2,L1,L).


%--------------------------------------------------------------
% Extensao do predicado, para obter o total gasto num dado servico
% custoServico: Id servico, Resultado -> {V,F}
custoServico(S,R):- solucoes(C,amed(D,I2,S,C),L2),
                    soma(L2,R).


%--------------------------------------------------------------
% Extensao do predicado, para obter a soma de todos os valores
% existentes numa lista
% soma: Lista, Resultado -> {V,F}
soma([],0).
soma([H|T],R):- soma(T,N),
                R is N+H.


%--------------------------------------------------------------
% Extensao do predicado, para obter o total gasto por um utente
% custoUtente: Id utente, Resultado -> {V,F}
custoUtente(U,R) :- solucoes(C,amed(_,U,_,C),L),
                    soma(L,R).


%--------------------------------------------------------------
% Extensao do meta-predicado remover: F -> {V,F}
remover(F) :- retract(F).
remover(F) :- assert(F), !, fail.

removerL([H|T]) :- retract(H),
                    removerL(T).
removerL([]).
removerL(H) :- assert(H), !, fail.


%--------------------------------------------------------------
% Extensao do meta-predicado involucao: F -> {V,F}
involucao(F) :- solucoes(I, -F::I, Li),
                remover(F),
                testar(Li).

involucaoL(excecao(utente(U,N,I,M))) :- solucoes(excecao(utente(U,X,Y,Z)), excecao(utente(U,X,Y,Z)), Li),
                                        removerL(Li).

involucaoL(excecao(cuiprest(U,D,I,C))) :- solucoes(excecao(cuiprest(U,X,Y,Z)), excecao(cuiprest(U,X,Y,Z)), Li),
                                        removerL(Li).

involucaoL(excecao(amed(D,U,S,P))) :- solucoes(excecao(amed(D,U,S,Z)), excecao(amed(D,U,S,Z)), Li),
                                      removerL(Li).
