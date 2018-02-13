%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% SIST. REPR. CONHECIMENTO E RACIOCINIO - MiEI/3
% Programacao em logica estendida
% Trabalho prático nº 1
%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% SICStus PROLOG: Declaracoes iniciais
:- set_prolog_flag( discontiguous_warnings,off ).
:- set_prolog_flag( single_var_warnings,off ).
:- set_prolog_flag( unknown,fail ).
:- op( 900,xfy,'::' ).
:-dynamic data/3.
:-dynamic utente/4.
:-dynamic nome/1.
:-dynamic descricao/1.
:-dynamic cidade/1.
:-dynamic morada/1.
:-dynamic instituicao/1.
:-dynamic cuiprest/4.
:-dynamic amed/4.

%--------------------------------------------------------------
% Extensao do meta-predicado nao: Questao {V,F}
nao(Q) :- Q, !, fail.
nao(Q).


%--------------------------------------------------------------
% Extensao do meta-predicado solucoes: F, Q, S -> {V,F}
solucoes(F, Q, S) :- findall(F, Q, S).


%--------------------------------------------------------------
% Extensao do predicado comprimento: L, N -> {V,F}
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
evolucao(F) :- solucoes(I, +F::I, Li),
               inserir(F),
               testar(Li).


%--------------------------------------------------------------
% Extensao do predicado morada: Morada -> {V,F}
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
-nome(N) :: fail.


%--------------------------------------------------------------
% Extensao do predicado utente: #IdUt, Nome, Idade, Morada -> {V,F}
utente(u1 , nome('joao miguel') , 30 , morada('rua de barros')).
utente(u2 , nome('bruno machado') , 20 , morada('rua de santa apolonia')).
utente(u3 , nome('carlos silva') , 20 , morada('rua do souto')).
utente(u4 , nome('paulo guedes') , 20 , morada('rua penedo da forca')).
utente(u5 , nome('goncalo moreira') , 20 , morada('rua padre francisco babo')).

% Invariante Referencial: nao admitir mais do que 1 utente
%                         com o mesmo id
+utente(U,N,I,M) :: (
                      solucoes( U , utente( U , _ , _ , _ ) , S ),
                      comprimento( S , T ),
                      T =< 1
                    ).
% Invariante Referencial: nao admitir remocao de utentes que
%                         estejam ligados a um ato medico
-utente(U,N,I,M) :: (
                      solucoes( U, amed( D, U, S, P), S),
                      comprimento(S,T),
                      T==0
                    ).


%--------------------------------------------------------------
% Extensão do predicado registarUtente que permite a evolucao
% do conhecimento de utentes
registarUtente(U,N,I,M):- evolucao(utente(U,N,I,M)),
                          N,
                          M.
registarUtente(U,N,I,M):- evolucao(utente(U,N,I,M)),
                          evolucao(N),
                          evolucao(M).
registarUtente(U,N,I,M):- evolucao(utente(U,N,I,M)),
                          N,
                          evolucao(M).
registarUtente(U,N,I,M):- evolucao(utente(U,N,I,M)),
                          evolucao(N),
                          M.


%--------------------------------------------------------------
% Extensão do predicado removerUtente que permite a regressao
% do conhecimento de utentes
removerUtente(U,N,I,M):- involucao(utente(U,N,I,M)).


%------------------------------------------------------
% Extensao do predicado descricao: Descricao -> {V,F}
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
                      solucoes( S , amed( _ , _ , S , _ ) , R ),
                      comprimento( R , T ),
                      T == 0
                    ).


%--------------------------------------------------------------
% Extensão do predicado registarCuiPrest que permite a evolucao
% do conhecimento de cuidados prestados
registarCuiPrest(U,D,I,C):- evolucao(cuiprest(U,D,I,C)),
                            D,
                            I,
                            C.
registarCuiPrest(U,D,I,C):- evolucao(cuiprest(U,D,I,C)),
                            evolucao(D),
                            evolucao(I),
                            evolucao(C).
registarCuiPrest(U,D,I,C):- evolucao(cuiprest(U,D,I,C)),
                            evolucao(D),
                            I,
                            C.
registarCuiPrest(U,D,I,C):- evolucao(cuiprest(U,D,I,C)),
                            D,
                            evolucao(I),
                            C.
registarCuiPrest(U,D,I,C):- evolucao(cuiprest(U,D,I,C)),
                            D,
                            I,
                            evolucao(C).
registarCuiPrest(U,D,I,C):- evolucao(cuiprest(U,D,I,C)),
                            evolucao(D),
                            evolucao(I),
                            C.
registarCuiPrest(U,D,I,C):- evolucao(cuiprest(U,D,I,C)),
                            evolucao(D),
                            I,
                            evolucao(C).
registarCuiPrest(U,D,I,C):- evolucao(cuiprest(U,D,I,C)),
                            D,
                            evolucao(I),
                            evolucao(C).


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
% Entensao do predicado ato médico: Data, #IdUt, #IdServ, Custo -> {V,F}
amed(data(21, 02, 2017) , u1 , c4 , 100).
amed(data(21, 02, 2017) , u1 , c2 , 100).
amed(data(12, 01, 2017) , u2 , c5 , 10).
amed(data(30, 01, 2017) , u3 , c3 , 5).
amed(data(24, 02, 2017) , u4 , c1 , 20).
amed(data(24, 02, 2017) , u3 , c1 , 20).
amed(data(15, 03, 2017) , u5 , c2 , 45).

% Invariante Referencial: nao admitir mais do que 1 ato medico
%                         com a mesma data e com o mesmo id de utente
%                         e cuidado prestado
+amed(D,I,I2,C) :: (
                      solucoes( (D, I, I2) , amed( D , I , I2 , _ ) , S ),
                      comprimento( S , T ),
                      T =< 1
                    ).


%----------------------------------------
% Extensão do predicado registarAmed que permite a evolucao
% do conhecimento de atos medicos
registaAMed(U,D,I,C) :- evolucao(amed(U,D,I,C)).


%----------------------------------------
% Extensão do predicado registarAmed que permite a regressao
% do conhecimento de atos medicos
removerAMed(U,D,I,C) :- involucao(amed(U,D,I,C)).


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


%----------------------------------------
% Extensao do meta-predicado remover: F -> {V,F}
remover(F) :- retract(F).
remover(F) :- assert(F), !, fail.


%----------------------------------------
% Extensao do meta-predicado evolucao: F -> {V,F}
involucao(F) :- solucoes(I, -F::I, Li),
                remover(F),
                testar(Li).
