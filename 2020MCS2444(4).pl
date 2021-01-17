/*ILFP Assignmnet 5: 
			Submitted By: AAYUSH KUMAR SINGH (2020MCS2444)
*/

/*Database for 5 generations from the novel "One Hundred Years Of Solitude*/
:- use_module(library(lists)).
male(joseArcadioBuendia).
female(ursulaIguaran).
female(rebeca).
male(joseArcadioBBuendia).
female(pilarTernera).
male(aurelianoBuendia).
female(remediosMoscote).
female(amaranta).
female(santaSofiaDeLaPiedad).
male(arcadio).
male(aurelianoJose).
female(remediosTheBeauty).
male(joseArcadioII).
female(petraCotes).
male(aurelianoII).
female(femandaDelCarpio).
male(gaston).
female(amarantaUrsula).
male(joseArcadio).
female(renataRemedios).
male(mauricioBabilonia).
male(aurelianoBabilonia).
male(aureliano).

married(joseArcadioBuendia, ursulaIguaran).
married(joseArcadioBBuendia, rebeca).
married(remediosMoscote , aurelianoBuendia).
married(arcadio ,santaSofiaDeLaPiedad).
married(aurelianoII, femandaDelCarpio).
married(gaston, amarantaUrsula).

child(joseArcadioBuendia, joseArcadioBBuendia).
child(joseArcadioBuendia, amaranta).
child(ursulaIguaran, joseArcadioBBuendia).
child(ursulaIguaran, amaranta).
child(joseArcadioBBuendia,arcadio).
child(pilarTernera, arcadio).
child(pilarTernera, aurelianoJose).
child(aurelianoBuendia, aurelianoJose).
child(santaSofiaDeLaPiedad, remediosTheBeauty).
child(santaSofiaDeLaPiedad, joseArcadioII).
child(santaSofiaDeLaPiedad, aurelianoII).
child(arcadio,joseArcadioII).
child(arcadio, remediosTheBeauty).
child(arcadio, aurelianoII).
child(aurelianoII, amarantaUrsula).
child(aurelianoII, joseArcadio).
child(aurelianoII, renataRemedios).
child(femandaDelCarpio, amarantaUrsula).
child(femandaDelCarpio, joseArcadio).
child(femandaDelCarpio, renataRemedios).
child(renataRemedios, aurelianoBabilonia).
child(mauricioBabilonia, aurelianoBabilonia).
child(amarantaUrsula, aureliano).
child(aurelianoBabilonia, aureliano).

/*Y is son/daughter of X*/
son(X,Y):- male(Y),child(X,Y).

daughter(X,Y):- female(Y),child(X,Y).

/*Y is father/mother of X*/
father(X,Y):- male(Y),child(Y,X).
mother(X,Y):- female(Y),child(Y,X).

/*Y is cousin of X*/
siblings(X,Y):- father(Y,Z),father(X,Z), Y\=X.
cousin(X,Y):- child(Z,Y),siblings(Z,W),child(W,X).

/*X is grandfather of Y*/
grandfather(X,Y):- male(X),child(Z,Y),child(X,Z).
grandmother(X,Y):- female(X),child(Z,Y),child(X,Z).

/*If Y is sister of X*/
sister(X,Y):- female(Y),father(Y,Z),child(Z,X), Y\=X.

/* If Y is brother of X*/
brother(X,Y):- male(Y),father(Y,Z),child(Z,X), Y\=X.

/*Uncle: Y is uncle of X*/
uncle(X,Y):- male(Y),child(Z,X),brother(Z,Y).

/*Aunt: Y is aunt of X*/
aunt(X,Y):- female(Y),child(Z,X),sister(Z,Y).

/*X is an ancestor of Y*/
ancestor(X,Y):- child(X,Y).
ancestor(X,Y):- child(X,Z), ancestor(Z,Y).

/*X is descendant of Y*/
descendant(X,Y):- ancestor(Y,X).

/* Test Cases and their respective Outputs:
i.	married(joseArcadioBuendia, X).
	X = ursulaIguaran.

ii.	child(joseArcadioBuendia, X).
	X = joseArcadioBBuendia.
	X = amaranta.

iii.	son(ursulaIguaran, X).
	X = joseArcadioBBuendia ;

iv. 	daughter(ursulaIguaran, X).
	X = amaranta ;

v.	father(X, aurelianoII).
	X = renataRemedios.
	X = joseArcadio ;
	X = amarantaUrsula ;

vi.	brother(X, aurelianoII).
	X = remediosTheBeauty ;
	X = joseArcadioII ;

vii.	sister(aurelianoII, X).
	X = remediosTheBeauty ;

viii.	uncle(joseArcadio, X).
	X = joseArcadioII ;

ix.	aunt(joseArcadio, X).
	X = remediosTheBeauty ;

x.	descendant(joseArcadio, X).
	X = arcadio ;
	X = santaSofiaDeLaPiedad ;
	X = pilarTernera ;
	X = joseArcadioBBuendia ;
	X = ursulaIguaran ;
	X = joseArcadioBuendia ;
	X = femandaDelCarpio ;
	X = aurelianoII ;

*/
