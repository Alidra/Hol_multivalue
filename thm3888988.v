Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3888988_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm11004_spec.
Require Import thm11005_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm1834_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm21735_spec.
Require Import thm21736_spec.
Require Import thm21742_spec.
Require Import thm21761_spec.
Require Import thm21763_spec.
Require Import thm21780_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Lemma lem3888010 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3888011 {_100554 : Type'} (x : _100554) : (@IN _100554 x (@EMPTY _100554)) = False.
Proof. exact (@lem3888010 _100554 x). Qed.
Lemma lem3888012 {_100554 : Type'} (a : _100554) : (@IN _100554 a (@EMPTY _100554)) = False.
Proof. exact (@lem3888011 _100554 a). Qed.
Lemma lem3888013 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3888014 {_100554 : Type'} (a : _100554) : (term0 _100554 a) = (~ False).
Proof. exact (MK_COMB (@lem3888013) (@lem3888012 _100554 a)). Qed.
Lemma lem3888016 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3888017 {_100554 : Type'} (a : _100554) : (term0 _100554 a) = True.
Proof. exact (TRANS (@lem3888014 _100554 a) (@lem3888016)). Qed.
Lemma lem3888018 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3888019 {_100554 : Type'} (a : _100554) : (term1 _100554 a) = (and True).
Proof. exact (MK_COMB (@lem3888018) (@lem3888017 _100554 a)). Qed.
Lemma lem3888020 (P : Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem3888021 {_100554 : Type'} (a : _100554) (P : Prop) : (term2 _100554 a P) = (True /\ P).
Proof. exact (MK_COMB (@lem3888019 _100554 a) (@lem3888020 P)). Qed.
Lemma lem3888023 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3888024 (P : Prop) : (True /\ P) = P.
Proof. exact (@lem3888023 P). Qed.
Lemma lem3888025 {_100554 : Type'} (a : _100554) (P : Prop) : (term2 _100554 a P) = P.
Proof. exact (TRANS (@lem3888021 _100554 a P) (@lem3888024 P)). Qed.
Lemma lem3888026 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3888027 {_100554 : Type'} (a : _100554) (P : Prop) : (term3 _100554 a P) = (@eq Prop P).
Proof. exact (MK_COMB (@lem3888026) (@lem3888025 _100554 a P)). Qed.
Lemma lem3888028 (P : Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem3888029 {_100554 : Type'} (a : _100554) (P : Prop) : ((term2 _100554 a P) = P) = (P = P).
Proof. exact (MK_COMB (@lem3888027 _100554 a P) (@lem3888028 P)). Qed.
Lemma lem3888031 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3888032 (x : Prop) : (x = x) = True.
Proof. exact (@lem3888031 Prop x). Qed.
Lemma lem3888033 (P : Prop) : (P = P) = True.
Proof. exact (@lem3888032 P). Qed.
Lemma lem3888034 {_100554 : Type'} (a : _100554) (P : Prop) : ((term2 _100554 a P) = P) = True.
Proof. exact (TRANS (@lem3888029 _100554 a P) (@lem3888033 P)). Qed.
Lemma lem3888035 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3888036 {_100554 : Type'} (a : _100554) (P : Prop) : (term4 _100554 a P) = (and True).
Proof. exact (MK_COMB (@lem3888035) (@lem3888034 _100554 a P)). Qed.
Lemma lem3888044 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term5 A x y s) = (term6 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3888045 {_100554 : Type'} (y : _100554) (x : _100554) (s : _100554 -> Prop) : (term5 _100554 x y s) = (term6 _100554 y x s).
Proof. exact (@lem3888044 _100554 y x s). Qed.
Lemma lem3888046 {_100554 : Type'} (b : _100554) (a : _100554) : (term7 _100554 a b) = (term8 _100554 b a).
Proof. exact (@lem3888045 _100554 b a (@EMPTY _100554)). Qed.
Lemma lem3888052 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3888053 {_100554 : Type'} (x : _100554) : (@IN _100554 x (@EMPTY _100554)) = False.
Proof. exact (@lem3888052 _100554 x). Qed.
Lemma lem3888054 {_100554 : Type'} (a : _100554) : (@IN _100554 a (@EMPTY _100554)) = False.
Proof. exact (@lem3888053 _100554 a). Qed.
Lemma lem3888055 {_100554 : Type'} (a : _100554) (b : _100554) : (term9 _100554 a b) = (term9 _100554 a b).
Proof. exact (eq_refl (term9 _100554 a b)). Qed.
Lemma lem3888056 {_100554 : Type'} (a : _100554) (b : _100554) : (term8 _100554 b a) = (term10 _100554 a b).
Proof. exact (MK_COMB (@lem3888055 _100554 a b) (@lem3888054 _100554 a)). Qed.
Lemma lem3888058 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem3888059 {_100554 : Type'} (a : _100554) (b : _100554) : (term10 _100554 a b) = (a = b).
Proof. exact (@lem3888058 (a = b)). Qed.
Lemma lem3888062 {_100554 : Type'} (a : _100554) (b : _100554) : (term8 _100554 b a) = (a = b).
Proof. exact (TRANS (@lem3888056 _100554 a b) (@lem3888059 _100554 a b)). Qed.
Lemma lem3888063 {_100554 : Type'} (a : _100554) (b : _100554) : (term7 _100554 a b) = (a = b).
Proof. exact (TRANS (@lem3888046 _100554 b a) (@lem3888062 _100554 a b)). Qed.
Lemma lem3888064 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3888065 {_100554 : Type'} (a : _100554) (b : _100554) : (term11 _100554 a b) = (term12 _100554 a b).
Proof. exact (MK_COMB (@lem3888064) (@lem3888063 _100554 a b)). Qed.
Lemma lem3888066 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3888067 {_100554 : Type'} (a : _100554) (b : _100554) : (term13 _100554 a b) = (term14 _100554 a b).
Proof. exact (MK_COMB (@lem3888066) (@lem3888065 _100554 a b)). Qed.
Lemma lem3888068 (P : Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem3888069 {_100554 : Type'} (a : _100554) (b : _100554) (P : Prop) : (term15 _100554 a b P) = (term16 _100554 a b P).
Proof. exact (MK_COMB (@lem3888067 _100554 a b) (@lem3888068 P)). Qed.
Lemma lem3888072 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3888073 {_100554 : Type'} (a : _100554) (b : _100554) (P : Prop) : (term17 _100554 a b P) = (term18 _100554 a b P).
Proof. exact (MK_COMB (@lem3888072) (@lem3888069 _100554 a b P)). Qed.
Lemma lem3888078 {_100554 : Type'} (a : _100554) (b : _100554) (P : Prop) : (term16 _100554 a b P) = (term16 _100554 a b P).
Proof. exact (eq_refl (term16 _100554 a b P)). Qed.
Lemma lem3888079 {_100554 : Type'} (a : _100554) (b : _100554) (P : Prop) : ((term15 _100554 a b P) = (term16 _100554 a b P)) = ((term16 _100554 a b P) = (term16 _100554 a b P)).
Proof. exact (MK_COMB (@lem3888073 _100554 a b P) (@lem3888078 _100554 a b P)). Qed.
Lemma lem3888081 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3888082 (x : Prop) : (x = x) = True.
Proof. exact (@lem3888081 Prop x). Qed.
Lemma lem3888083 {_100554 : Type'} (a : _100554) (b : _100554) (P : Prop) : ((term16 _100554 a b P) = (term16 _100554 a b P)) = True.
Proof. exact (@lem3888082 (term16 _100554 a b P)). Qed.
Lemma lem3888084 {_100554 : Type'} (a : _100554) (b : _100554) (P : Prop) : ((term15 _100554 a b P) = (term16 _100554 a b P)) = True.
Proof. exact (TRANS (@lem3888079 _100554 a b P) (@lem3888083 _100554 a b P)). Qed.
Lemma lem3888085 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3888086 {_100554 : Type'} (a : _100554) (b : _100554) (P : Prop) : (term19 _100554 a b P) = (and True).
Proof. exact (MK_COMB (@lem3888085) (@lem3888084 _100554 a b P)). Qed.
Lemma lem3888092 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term5 A x y s) = (term6 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3888093 {_100554 : Type'} (y : _100554) (x : _100554) (s : _100554 -> Prop) : (term5 _100554 x y s) = (term6 _100554 y x s).
Proof. exact (@lem3888092 _100554 y x s). Qed.
Lemma lem3888094 {_100554 : Type'} (b : _100554) (a : _100554) (cs : _100554 -> Prop) : (term5 _100554 a b cs) = (term6 _100554 b a cs).
Proof. exact (@lem3888093 _100554 b a cs). Qed.
Lemma lem3888100 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3888101 {_100554 : Type'} (P : _100554 -> Prop) (x : _100554) : (@IN _100554 x P) = (P x).
Proof. exact (@lem3888100 _100554 P x). Qed.
Lemma lem3888102 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) : (@IN _100554 a cs) = (cs a).
Proof. exact (@lem3888101 _100554 cs a). Qed.
Lemma lem3888103 {_100554 : Type'} (a : _100554) (b : _100554) : (term9 _100554 a b) = (term9 _100554 a b).
Proof. exact (eq_refl (term9 _100554 a b)). Qed.
Lemma lem3888104 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) : (term6 _100554 b a cs) = (term20 _100554 b cs a).
Proof. exact (MK_COMB (@lem3888103 _100554 a b) (@lem3888102 _100554 cs a)). Qed.
Lemma lem3888107 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) : (term5 _100554 a b cs) = (term20 _100554 b cs a).
Proof. exact (TRANS (@lem3888094 _100554 b a cs) (@lem3888104 _100554 b cs a)). Qed.
Lemma lem3888108 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3888109 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) : (term21 _100554 a b cs) = (term22 _100554 b cs a).
Proof. exact (MK_COMB (@lem3888108) (@lem3888107 _100554 b cs a)). Qed.
Lemma lem3888110 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3888111 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) : (term23 _100554 a b cs) = (term24 _100554 b cs a).
Proof. exact (MK_COMB (@lem3888110) (@lem3888109 _100554 b cs a)). Qed.
Lemma lem3888112 (P : Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem3888113 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) : (term25 _100554 a b cs P) = (term26 _100554 b cs a P).
Proof. exact (MK_COMB (@lem3888111 _100554 b cs a) (@lem3888112 P)). Qed.
Lemma lem3888116 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3888117 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) : (term27 _100554 a b cs P) = (term28 _100554 b cs a P).
Proof. exact (MK_COMB (@lem3888116) (@lem3888113 _100554 b cs a P)). Qed.
Lemma lem3888125 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3888126 {_100554 : Type'} (P : _100554 -> Prop) (x : _100554) : (@IN _100554 x P) = (P x).
Proof. exact (@lem3888125 _100554 P x). Qed.
Lemma lem3888127 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) : (@IN _100554 a cs) = (cs a).
Proof. exact (@lem3888126 _100554 cs a). Qed.
Lemma lem3888128 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3888129 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) : (term29 _100554 a cs) = (term30 _100554 cs a).
Proof. exact (MK_COMB (@lem3888128) (@lem3888127 _100554 cs a)). Qed.
Lemma lem3888130 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3888131 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) : (term31 _100554 a cs) = (term32 _100554 cs a).
Proof. exact (MK_COMB (@lem3888130) (@lem3888129 _100554 cs a)). Qed.
Lemma lem3888132 (P : Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem3888133 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (P : Prop) : (term33 _100554 a cs P) = (term34 _100554 cs a P).
Proof. exact (MK_COMB (@lem3888131 _100554 cs a) (@lem3888132 P)). Qed.
Lemma lem3888136 {_100554 : Type'} (a : _100554) (b : _100554) : (term14 _100554 a b) = (term14 _100554 a b).
Proof. exact (eq_refl (term14 _100554 a b)). Qed.
Lemma lem3888137 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) : (term35 _100554 b a cs P) = (term36 _100554 b cs a P).
Proof. exact (MK_COMB (@lem3888136 _100554 a b) (@lem3888133 _100554 cs a P)). Qed.
Lemma lem3888140 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) : ((term25 _100554 a b cs P) = (term35 _100554 b a cs P)) = ((term26 _100554 b cs a P) = (term36 _100554 b cs a P)).
Proof. exact (MK_COMB (@lem3888117 _100554 b cs a P) (@lem3888137 _100554 b cs a P)). Qed.
Lemma lem3888143 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) : (term37 _100554 b a cs P) = (term38 _100554 b cs a P).
Proof. exact (MK_COMB (@lem3888086 _100554 a b P) (@lem3888140 _100554 b cs a P)). Qed.
Lemma lem3888145 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3888146 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) : (term38 _100554 b cs a P) = ((term26 _100554 b cs a P) = (term36 _100554 b cs a P)).
Proof. exact (@lem3888145 ((term26 _100554 b cs a P) = (term36 _100554 b cs a P))). Qed.
Lemma lem3888161 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) : (term37 _100554 b a cs P) = ((term26 _100554 b cs a P) = (term36 _100554 b cs a P)).
Proof. exact (TRANS (@lem3888143 _100554 b cs a P) (@lem3888146 _100554 b cs a P)). Qed.
Lemma lem3888162 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) : (term39 _100554 b a cs P) = (term38 _100554 b cs a P).
Proof. exact (MK_COMB (@lem3888036 _100554 a P) (@lem3888161 _100554 b cs a P)). Qed.
Lemma lem3888164 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3888165 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) : (term38 _100554 b cs a P) = ((term26 _100554 b cs a P) = (term36 _100554 b cs a P)).
Proof. exact (@lem3888164 ((term26 _100554 b cs a P) = (term36 _100554 b cs a P))). Qed.
Lemma lem3888180 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) : (term39 _100554 b a cs P) = ((term26 _100554 b cs a P) = (term36 _100554 b cs a P)).
Proof. exact (TRANS (@lem3888162 _100554 b cs a P) (@lem3888165 _100554 b cs a P)). Qed.
Lemma lem3888181 {_100554 : Type'} (b : _100554) (a : _100554) (cs : _100554 -> Prop) (P : Prop) : ((term26 _100554 b cs a P) = (term36 _100554 b cs a P)) = (term39 _100554 b a cs P).
Proof. exact (SYM (@lem3888180 _100554 b cs a P)). Qed.
Lemma lem3888183 (p : Prop) : p = (term40 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3888184 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) : ((term26 _100554 b cs a P) = (term36 _100554 b cs a P)) = (term41 _100554 b cs a P).
Proof. exact (@lem3888183 ((term26 _100554 b cs a P) = (term36 _100554 b cs a P))). Qed.
Lemma lem3888185 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) : (term41 _100554 b cs a P) = ((term26 _100554 b cs a P) = (term36 _100554 b cs a P)).
Proof. exact (SYM (@lem3888184 _100554 b cs a P)). Qed.
Lemma lem3888186 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) (h1 : term42 _100554 b cs a P) : term42 _100554 b cs a P.
Proof. exact (h1). Qed.
Lemma lem3888189 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) (h1 : term41 _100554 b cs a P) : term41 _100554 b cs a P.
Proof. exact (h1). Qed.
Lemma lem3888190 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) : term43 _100554 b cs a P.
Proof. exact (fun h0 : term41 _100554 b cs a P => @lem3888189 _100554 b cs a P h0). Qed.
Lemma lem3888191 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) (h1 : term43 _100554 b cs a P) : term43 _100554 b cs a P.
Proof. exact (h1). Qed.
Lemma lem3888192 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) (h1 : term41 _100554 b cs a P) : term41 _100554 b cs a P.
Proof. exact (h1). Qed.
Lemma lem3888193 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) (h1 : term41 _100554 b cs a P) (h2 : term43 _100554 b cs a P) : term41 _100554 b cs a P.
Proof. exact (@lem3888191 _100554 b cs a P h2 (@lem3888192 _100554 b cs a P h1)). Qed.
Lemma lem3888194 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) (h1 : term41 _100554 b cs a P) : term44 _100554 b cs a P.
Proof. exact (fun h0 : term43 _100554 b cs a P => @lem3888193 _100554 b cs a P h1 h0). Qed.
Lemma lem3888195 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) (h1 : term43 _100554 b cs a P) : term43 _100554 b cs a P.
Proof. exact (h1). Qed.
Lemma lem3888196 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) (h1 : term41 _100554 b cs a P) (h2 : term43 _100554 b cs a P) : term41 _100554 b cs a P.
Proof. exact (@lem3888194 _100554 b cs a P h1 (@lem3888195 _100554 b cs a P h2)). Qed.
Lemma lem3888197 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) (h1 : term43 _100554 b cs a P) : term43 _100554 b cs a P.
Proof. exact (fun h0 : term41 _100554 b cs a P => @lem3888196 _100554 b cs a P h0 h1). Qed.
Lemma lem3888198 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) : term45 _100554 b cs a P.
Proof. exact (fun h0 : term43 _100554 b cs a P => @lem3888197 _100554 b cs a P h0). Qed.
Lemma lem3888201 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) : term43 _100554 b cs a P.
Proof. exact (@lem3888198 _100554 b cs a P (@lem3888190 _100554 b cs a P)). Qed.
Lemma lem3888202 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) : term43 _100554 b cs a P.
Proof. exact (@lem3888201 _100554 b cs a P). Qed.
Lemma lem3888220 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3888221 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) : (term41 _100554 b cs a P) = (term46 _100554 b cs a P).
Proof. exact (@lem3888220 (term42 _100554 b cs a P)). Qed.
Lemma lem3888223 (t : Prop) : (term47 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3888224 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) : (term46 _100554 b cs a P) = ((term26 _100554 b cs a P) = (term36 _100554 b cs a P)).
Proof. exact (@lem3888223 ((term26 _100554 b cs a P) = (term36 _100554 b cs a P))). Qed.
Lemma lem3888225 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) : (term41 _100554 b cs a P) = ((term26 _100554 b cs a P) = (term36 _100554 b cs a P)).
Proof. exact (TRANS (@lem3888221 _100554 b cs a P) (@lem3888224 _100554 b cs a P)). Qed.
Lemma lem3888234 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (P : Prop) : (term48 _100554 cs a P) = (term49 _100554 cs a P).
Proof. exact (fun_ext (fun b : _100554 => @lem3888225 _100554 b cs a P)). Qed.
Lemma lem3888235 {_100554 : Type'} : (@all _100554) = (@all _100554).
Proof. exact (eq_refl (@all _100554)). Qed.
Lemma lem3888236 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (P : Prop) : (term50 _100554 cs a P) = (term51 _100554 cs a P).
Proof. exact (MK_COMB (@lem3888235 _100554) (@lem3888234 _100554 cs a P)). Qed.
Lemma lem3888241 {_100554 : Type'} (a : _100554) (P : Prop) : (term52 _100554 a P) = (term53 _100554 a P).
Proof. exact (fun_ext (fun cs : _100554 -> Prop => @lem3888236 _100554 cs a P)). Qed.
Lemma lem3888242 {_100554 : Type'} : (@all (_100554 -> Prop)) = (@all (_100554 -> Prop)).
Proof. exact (eq_refl (@all (_100554 -> Prop))). Qed.
Lemma lem3888243 {_100554 : Type'} (a : _100554) (P : Prop) : (term54 _100554 a P) = (term55 _100554 a P).
Proof. exact (MK_COMB (@lem3888242 _100554) (@lem3888241 _100554 a P)). Qed.
Lemma lem3888248 {_100554 : Type'} (P : Prop) : (term56 _100554 P) = (term57 _100554 P).
Proof. exact (fun_ext (fun a : _100554 => @lem3888243 _100554 a P)). Qed.
Lemma lem3888249 {_100554 : Type'} : (@all _100554) = (@all _100554).
Proof. exact (eq_refl (@all _100554)). Qed.
Lemma lem3888250 {_100554 : Type'} (P : Prop) : (term58 _100554 P) = (term59 _100554 P).
Proof. exact (MK_COMB (@lem3888249 _100554) (@lem3888248 _100554 P)). Qed.
Lemma lem3888255 {_100554 : Type'} : (term60 _100554) = (term61 _100554).
Proof. exact (fun_ext (fun P : Prop => @lem3888250 _100554 P)). Qed.
Lemma lem3888256 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem3888265 {_100554 : Type'} : (term62 _100554) = (term63 _100554).
Proof. exact (MK_COMB (@lem3888256) (@lem3888255 _100554)). Qed.
Lemma lem3888292 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) : ((term26 _100554 b cs a P) = (term36 _100554 b cs a P)) = ((term26 _100554 b cs a P) = (term36 _100554 b cs a P)).
Proof. exact (eq_refl ((term26 _100554 b cs a P) = (term36 _100554 b cs a P))). Qed.
Lemma lem3888293 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (P : Prop) : (term49 _100554 cs a P) = (term49 _100554 cs a P).
Proof. exact (fun_ext (fun b : _100554 => @lem3888292 _100554 b cs a P)). Qed.
Lemma lem3888294 {_100554 : Type'} : (@all _100554) = (@all _100554).
Proof. exact (eq_refl (@all _100554)). Qed.
Lemma lem3888295 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (P : Prop) : (term51 _100554 cs a P) = (term51 _100554 cs a P).
Proof. exact (MK_COMB (@lem3888294 _100554) (@lem3888293 _100554 cs a P)). Qed.
Lemma lem3888296 {_100554 : Type'} (a : _100554) (P : Prop) : (term53 _100554 a P) = (term53 _100554 a P).
Proof. exact (fun_ext (fun cs : _100554 -> Prop => @lem3888295 _100554 cs a P)). Qed.
Lemma lem3888297 {_100554 : Type'} : (@all (_100554 -> Prop)) = (@all (_100554 -> Prop)).
Proof. exact (eq_refl (@all (_100554 -> Prop))). Qed.
Lemma lem3888298 {_100554 : Type'} (a : _100554) (P : Prop) : (term55 _100554 a P) = (term55 _100554 a P).
Proof. exact (MK_COMB (@lem3888297 _100554) (@lem3888296 _100554 a P)). Qed.
Lemma lem3888299 {_100554 : Type'} (P : Prop) : (term57 _100554 P) = (term57 _100554 P).
Proof. exact (fun_ext (fun a : _100554 => @lem3888298 _100554 a P)). Qed.
Lemma lem3888300 {_100554 : Type'} : (@all _100554) = (@all _100554).
Proof. exact (eq_refl (@all _100554)). Qed.
Lemma lem3888301 {_100554 : Type'} (P : Prop) : (term59 _100554 P) = (term59 _100554 P).
Proof. exact (MK_COMB (@lem3888300 _100554) (@lem3888299 _100554 P)). Qed.
Lemma lem3888302 {_100554 : Type'} : (term61 _100554) = (term61 _100554).
Proof. exact (fun_ext (fun P : Prop => @lem3888301 _100554 P)). Qed.
Lemma lem3888303 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem3888304 {_100554 : Type'} : (term63 _100554) = (term63 _100554).
Proof. exact (MK_COMB (@lem3888303) (@lem3888302 _100554)). Qed.
Lemma lem3888305 {_100554 : Type'} : (term62 _100554) = (term63 _100554).
Proof. exact (TRANS (@lem3888265 _100554) (@lem3888304 _100554)). Qed.
Lemma lem3888311 (P : Prop -> Prop) : (term64 P) = (term65 P).
Proof. exact (EQ_MP (@lem11005 P) (@lem11004 P)). Qed.
Lemma lem3888312 {_100554 : Type'} : (term66 _100554) = (term67 _100554).
Proof. exact (@lem3888311 (term61 _100554)). Qed.
Lemma lem3888313 {_100554 : Type'} (P : Prop) : (term68 _100554 P) = (term59 _100554 P).
Proof. exact (eq_refl (term68 _100554 P)). Qed.
Lemma lem3888314 {_100554 : Type'} : (term69 _100554) = (term61 _100554).
Proof. exact (fun_ext (fun P : Prop => @lem3888313 _100554 P)). Qed.
Lemma lem3888315 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem3888316 {_100554 : Type'} : (term66 _100554) = (term63 _100554).
Proof. exact (MK_COMB (@lem3888315) (@lem3888314 _100554)). Qed.
Lemma lem3888317 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3888318 {_100554 : Type'} : (term70 _100554) = (term71 _100554).
Proof. exact (MK_COMB (@lem3888317) (@lem3888316 _100554)). Qed.
Lemma lem3888319 {_100554 : Type'} : (term72 _100554) = (term73 _100554).
Proof. exact (eq_refl (term72 _100554)). Qed.
Lemma lem3888320 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3888321 {_100554 : Type'} : (term74 _100554) = (term75 _100554).
Proof. exact (MK_COMB (@lem3888320) (@lem3888319 _100554)). Qed.
Lemma lem3888322 {_100554 : Type'} : (term76 _100554) = (term77 _100554).
Proof. exact (eq_refl (term76 _100554)). Qed.
Lemma lem3888323 {_100554 : Type'} : (term67 _100554) = (term78 _100554).
Proof. exact (MK_COMB (@lem3888321 _100554) (@lem3888322 _100554)). Qed.
Lemma lem3888324 {_100554 : Type'} : ((term66 _100554) = (term67 _100554)) = ((term63 _100554) = (term78 _100554)).
Proof. exact (MK_COMB (@lem3888318 _100554) (@lem3888323 _100554)). Qed.
Lemma lem3888325 {_100554 : Type'} : (term63 _100554) = (term78 _100554).
Proof. exact (EQ_MP (@lem3888324 _100554) (@lem3888312 _100554)). Qed.
Lemma lem3888347 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem21761 t)). Qed.
Lemma lem3888348 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) : (term79 _100554 b cs a) = (term22 _100554 b cs a).
Proof. exact (@lem3888347 (term22 _100554 b cs a)). Qed.
Lemma lem3888351 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3888352 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) : (term80 _100554 b cs a) = (term81 _100554 b cs a).
Proof. exact (MK_COMB (@lem3888351) (@lem3888348 _100554 b cs a)). Qed.
Lemma lem3888356 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem21761 t)). Qed.
Lemma lem3888357 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) : (term82 _100554 cs a) = (term30 _100554 cs a).
Proof. exact (@lem3888356 (term30 _100554 cs a)). Qed.
Lemma lem3888358 {_100554 : Type'} (a : _100554) (b : _100554) : (term14 _100554 a b) = (term14 _100554 a b).
Proof. exact (eq_refl (term14 _100554 a b)). Qed.
Lemma lem3888359 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) : (term83 _100554 b cs a) = (term84 _100554 b cs a).
Proof. exact (MK_COMB (@lem3888358 _100554 a b) (@lem3888357 _100554 cs a)). Qed.
Lemma lem3888362 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) : ((term79 _100554 b cs a) = (term83 _100554 b cs a)) = ((term22 _100554 b cs a) = (term84 _100554 b cs a)).
Proof. exact (MK_COMB (@lem3888352 _100554 b cs a) (@lem3888359 _100554 b cs a)). Qed.
Lemma lem3888363 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) : (term85 _100554 cs a) = (term86 _100554 cs a).
Proof. exact (fun_ext (fun b : _100554 => @lem3888362 _100554 b cs a)). Qed.
Lemma lem3888364 {_100554 : Type'} : (@all _100554) = (@all _100554).
Proof. exact (eq_refl (@all _100554)). Qed.
Lemma lem3888365 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) : (term87 _100554 cs a) = (term88 _100554 cs a).
Proof. exact (MK_COMB (@lem3888364 _100554) (@lem3888363 _100554 cs a)). Qed.
Lemma lem3888372 {_100554 : Type'} (a : _100554) : (term89 _100554 a) = (term90 _100554 a).
Proof. exact (fun_ext (fun cs : _100554 -> Prop => @lem3888365 _100554 cs a)). Qed.
Lemma lem3888373 {_100554 : Type'} : (@all (_100554 -> Prop)) = (@all (_100554 -> Prop)).
Proof. exact (eq_refl (@all (_100554 -> Prop))). Qed.
Lemma lem3888374 {_100554 : Type'} (a : _100554) : (term91 _100554 a) = (term92 _100554 a).
Proof. exact (MK_COMB (@lem3888373 _100554) (@lem3888372 _100554 a)). Qed.
Lemma lem3888381 {_100554 : Type'} : (term93 _100554) = (term94 _100554).
Proof. exact (fun_ext (fun a : _100554 => @lem3888374 _100554 a)). Qed.
Lemma lem3888382 {_100554 : Type'} : (@all _100554) = (@all _100554).
Proof. exact (eq_refl (@all _100554)). Qed.
Lemma lem3888383 {_100554 : Type'} : (term73 _100554) = (term95 _100554).
Proof. exact (MK_COMB (@lem3888382 _100554) (@lem3888381 _100554)). Qed.
Lemma lem3888390 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3888391 {_100554 : Type'} : (term75 _100554) = (term96 _100554).
Proof. exact (MK_COMB (@lem3888390) (@lem3888383 _100554)). Qed.
Lemma lem3888411 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem21763 t)). Qed.
Lemma lem3888412 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) : (term97 _100554 b cs a) = False.
Proof. exact (@lem3888411 (term22 _100554 b cs a)). Qed.
Lemma lem3888413 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3888414 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) : (term98 _100554 b cs a) = (@eq Prop False).
Proof. exact (MK_COMB (@lem3888413) (@lem3888412 _100554 b cs a)). Qed.
Lemma lem3888418 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem21763 t)). Qed.
Lemma lem3888419 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) : (term99 _100554 cs a) = False.
Proof. exact (@lem3888418 (term30 _100554 cs a)). Qed.
Lemma lem3888420 {_100554 : Type'} (a : _100554) (b : _100554) : (term14 _100554 a b) = (term14 _100554 a b).
Proof. exact (eq_refl (term14 _100554 a b)). Qed.
Lemma lem3888421 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (b : _100554) : (term100 _100554 b cs a) = (term101 _100554 a b).
Proof. exact (MK_COMB (@lem3888420 _100554 a b) (@lem3888419 _100554 cs a)). Qed.
Lemma lem3888423 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem21763 t)). Qed.
Lemma lem3888424 {_100554 : Type'} (a : _100554) (b : _100554) : (term101 _100554 a b) = False.
Proof. exact (@lem3888423 (term12 _100554 a b)). Qed.
Lemma lem3888425 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) : (term100 _100554 b cs a) = False.
Proof. exact (TRANS (@lem3888421 _100554 cs a b) (@lem3888424 _100554 a b)). Qed.
Lemma lem3888426 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) : ((term97 _100554 b cs a) = (term100 _100554 b cs a)) = (False = False).
Proof. exact (MK_COMB (@lem3888414 _100554 b cs a) (@lem3888425 _100554 b cs a)). Qed.
Lemma lem3888428 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem21742 t)). Qed.
Lemma lem3888429 : (False = False) = (~ False).
Proof. exact (@lem3888428 False). Qed.
Lemma lem3888431 : (~ False) = True.
Proof. exact (proj2 (@lem21780)). Qed.
Lemma lem3888432 : (False = False) = True.
Proof. exact (TRANS (@lem3888429) (@lem3888431)). Qed.
Lemma lem3888433 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) : ((term97 _100554 b cs a) = (term100 _100554 b cs a)) = True.
Proof. exact (TRANS (@lem3888426 _100554 b cs a) (@lem3888432)). Qed.
Lemma lem3888434 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) : (term102 _100554 cs a) = (term103 _100554).
Proof. exact (fun_ext (fun b : _100554 => @lem3888433 _100554 b cs a)). Qed.
Lemma lem3888435 {_100554 : Type'} : (@all _100554) = (@all _100554).
Proof. exact (eq_refl (@all _100554)). Qed.
Lemma lem3888436 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) : (term104 _100554 cs a) = (term105 _100554).
Proof. exact (MK_COMB (@lem3888435 _100554) (@lem3888434 _100554 cs a)). Qed.
Lemma lem3888438 {A : Type'} (t : Prop) : (term106 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem3888439 {_100554 : Type'} (t : Prop) : (term106 _100554 t) = t.
Proof. exact (@lem3888438 _100554 t). Qed.
Lemma lem3888440 {_100554 : Type'} : (term105 _100554) = True.
Proof. exact (@lem3888439 _100554 True). Qed.
Lemma lem3888441 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) : (term104 _100554 cs a) = True.
Proof. exact (TRANS (@lem3888436 _100554 cs a) (@lem3888440 _100554)). Qed.
Lemma lem3888442 {_100554 : Type'} (a : _100554) : (term107 _100554 a) = (term108 _100554).
Proof. exact (fun_ext (fun cs : _100554 -> Prop => @lem3888441 _100554 cs a)). Qed.
Lemma lem3888443 {_100554 : Type'} : (@all (_100554 -> Prop)) = (@all (_100554 -> Prop)).
Proof. exact (eq_refl (@all (_100554 -> Prop))). Qed.
Lemma lem3888444 {_100554 : Type'} (a : _100554) : (term109 _100554 a) = (term110 _100554).
Proof. exact (MK_COMB (@lem3888443 _100554) (@lem3888442 _100554 a)). Qed.
Lemma lem3888446 {A : Type'} (t : Prop) : (term106 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem3888447 {_100554 : Type'} (t : Prop) : (term111 _100554 t) = t.
Proof. exact (@lem3888446 (_100554 -> Prop) t). Qed.
Lemma lem3888448 {_100554 : Type'} : (term110 _100554) = True.
Proof. exact (@lem3888447 _100554 True). Qed.
Lemma lem3888449 {_100554 : Type'} (a : _100554) : (term109 _100554 a) = True.
Proof. exact (TRANS (@lem3888444 _100554 a) (@lem3888448 _100554)). Qed.
Lemma lem3888450 {_100554 : Type'} : (term112 _100554) = (term103 _100554).
Proof. exact (fun_ext (fun a : _100554 => @lem3888449 _100554 a)). Qed.
Lemma lem3888451 {_100554 : Type'} : (@all _100554) = (@all _100554).
Proof. exact (eq_refl (@all _100554)). Qed.
Lemma lem3888452 {_100554 : Type'} : (term77 _100554) = (term105 _100554).
Proof. exact (MK_COMB (@lem3888451 _100554) (@lem3888450 _100554)). Qed.
Lemma lem3888454 {A : Type'} (t : Prop) : (term106 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem3888455 {_100554 : Type'} (t : Prop) : (term106 _100554 t) = t.
Proof. exact (@lem3888454 _100554 t). Qed.
Lemma lem3888456 {_100554 : Type'} : (term105 _100554) = True.
Proof. exact (@lem3888455 _100554 True). Qed.
Lemma lem3888457 {_100554 : Type'} : (term77 _100554) = True.
Proof. exact (TRANS (@lem3888452 _100554) (@lem3888456 _100554)). Qed.
Lemma lem3888458 {_100554 : Type'} : (term78 _100554) = (term113 _100554).
Proof. exact (MK_COMB (@lem3888391 _100554) (@lem3888457 _100554)). Qed.
Lemma lem3888460 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem21761 t)). Qed.
Lemma lem3888461 {_100554 : Type'} : (term113 _100554) = (term95 _100554).
Proof. exact (@lem3888460 (term95 _100554)). Qed.
Lemma lem3888484 {_100554 : Type'} : (term78 _100554) = (term95 _100554).
Proof. exact (TRANS (@lem3888458 _100554) (@lem3888461 _100554)). Qed.
Lemma lem3888485 {_100554 : Type'} : (term63 _100554) = (term95 _100554).
Proof. exact (TRANS (@lem3888325 _100554) (@lem3888484 _100554)). Qed.
Lemma lem3888486 {_100554 : Type'} : (term62 _100554) = (term95 _100554).
Proof. exact (TRANS (@lem3888305 _100554) (@lem3888485 _100554)). Qed.
Lemma lem3888487 {_100554 : Type'} : (term95 _100554) = (term62 _100554).
Proof. exact (SYM (@lem3888486 _100554)). Qed.
Lemma lem3888489 (p : Prop) : p = (term40 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3888490 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) : ((term22 _100554 b cs a) = (term84 _100554 b cs a)) = (term114 _100554 b cs a).
Proof. exact (@lem3888489 ((term22 _100554 b cs a) = (term84 _100554 b cs a))). Qed.
Lemma lem3888491 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) : (term114 _100554 b cs a) = ((term22 _100554 b cs a) = (term84 _100554 b cs a)).
Proof. exact (SYM (@lem3888490 _100554 b cs a)). Qed.
Lemma lem3888492 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : term115 _100554 b cs a) : term115 _100554 b cs a.
Proof. exact (h1). Qed.
Lemma lem3888501 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) : (term22 _100554 b cs a) = (term84 _100554 b cs a).
Proof. exact (@lem17160 (a = b) (cs a)). Qed.
Lemma lem3888506 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) : (term116 _100554 b cs a) = (term20 _100554 b cs a).
Proof. exact (@lem16933 (term20 _100554 b cs a)). Qed.
Lemma lem3888510 {_100554 : Type'} (a : _100554) (b : _100554) : (term117 _100554 a b) = (a = b).
Proof. exact (@lem16933 (a = b)). Qed.
Lemma lem3888514 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) : (term118 _100554 cs a) = (cs a).
Proof. exact (@lem16933 (cs a)). Qed.
Lemma lem3888515 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3888516 {_100554 : Type'} (a : _100554) (b : _100554) : (term119 _100554 a b) = (term9 _100554 a b).
Proof. exact (MK_COMB (@lem3888515) (@lem3888510 _100554 a b)). Qed.
Lemma lem3888517 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) : (term120 _100554 b cs a) = (term20 _100554 b cs a).
Proof. exact (MK_COMB (@lem3888516 _100554 a b) (@lem3888514 _100554 cs a)). Qed.
Lemma lem3888518 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) : (term121 _100554 b cs a) = (term120 _100554 b cs a).
Proof. exact (@lem17045 (term12 _100554 a b) (term30 _100554 cs a)). Qed.
Lemma lem3888519 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) : (term121 _100554 b cs a) = (term20 _100554 b cs a).
Proof. exact (TRANS (@lem3888518 _100554 b cs a) (@lem3888517 _100554 b cs a)). Qed.
Lemma lem3888522 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) : (term84 _100554 b cs a) = (term84 _100554 b cs a).
Proof. exact (eq_refl (term84 _100554 b cs a)). Qed.
Lemma lem3888523 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3888524 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) : (term122 _100554 b cs a) = (term123 _100554 b cs a).
Proof. exact (MK_COMB (@lem3888523) (@lem3888506 _100554 b cs a)). Qed.
Lemma lem3888525 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) : (term124 _100554 b cs a) = (term125 _100554 b cs a).
Proof. exact (MK_COMB (@lem3888524 _100554 b cs a) (@lem3888522 _100554 b cs a)). Qed.
Lemma lem3888526 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3888527 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) : (term24 _100554 b cs a) = (term126 _100554 b cs a).
Proof. exact (MK_COMB (@lem3888526) (@lem3888501 _100554 b cs a)). Qed.
Lemma lem3888528 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) : (term127 _100554 b cs a) = (term128 _100554 b cs a).
Proof. exact (MK_COMB (@lem3888527 _100554 b cs a) (@lem3888519 _100554 b cs a)). Qed.
Lemma lem3888529 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3888530 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) : (term129 _100554 b cs a) = (term130 _100554 b cs a).
Proof. exact (MK_COMB (@lem3888529) (@lem3888528 _100554 b cs a)). Qed.
Lemma lem3888531 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) : (term131 _100554 b cs a) = (term132 _100554 b cs a).
Proof. exact (MK_COMB (@lem3888530 _100554 b cs a) (@lem3888525 _100554 b cs a)). Qed.
Lemma lem3888532 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) : (term115 _100554 b cs a) = (term131 _100554 b cs a).
Proof. exact (@lem17646 (term22 _100554 b cs a) (term84 _100554 b cs a)). Qed.
Lemma lem3888537 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) : (term115 _100554 b cs a) = (term132 _100554 b cs a).
Proof. exact (TRANS (@lem3888532 _100554 b cs a) (@lem3888531 _100554 b cs a)). Qed.
Lemma lem3888600 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : term115 _100554 b cs a) : term132 _100554 b cs a.
Proof. exact (EQ_MP (@lem3888537 _100554 b cs a) (@lem3888492 _100554 b cs a h1)). Qed.
Lemma lem3888601 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : term128 _100554 b cs a) : term128 _100554 b cs a.
Proof. exact (h1). Qed.
Lemma lem3888602 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : term125 _100554 b cs a) : term125 _100554 b cs a.
Proof. exact (h1). Qed.
Lemma lem3888603 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : term128 _100554 b cs a) : term20 _100554 b cs a.
Proof. exact (proj2 (@lem3888601 _100554 b cs a h1)). Qed.
Lemma lem3888604 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : term128 _100554 b cs a) : term84 _100554 b cs a.
Proof. exact (proj1 (@lem3888601 _100554 b cs a h1)). Qed.
Lemma lem3888609 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : term125 _100554 b cs a) : term84 _100554 b cs a.
Proof. exact (proj2 (@lem3888602 _100554 b cs a h1)). Qed.
Lemma lem3888610 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : term125 _100554 b cs a) : term20 _100554 b cs a.
Proof. exact (proj1 (@lem3888602 _100554 b cs a h1)). Qed.
Lemma lem3888626 {_100554 : Type'} (a : _100554) (b : _100554) (h1 : a = b) : a = b.
Proof. exact (h1). Qed.
Lemma lem3888638 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (h1 : cs a) : cs a.
Proof. exact (h1). Qed.
Lemma lem3888650 {_100554 : Type'} (a : _100554) (b : _100554) (h1 : a = b) : a = b.
Proof. exact (h1). Qed.
Lemma lem3888662 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (h1 : cs a) : cs a.
Proof. exact (h1). Qed.
Lemma lem3888664 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : term128 _100554 b cs a) : term12 _100554 a b.
Proof. exact (proj1 (@lem3888604 _100554 b cs a h1)). Qed.
Lemma lem3888668 {_100554 : Type'} (a : _100554) (b : _100554) (h1 : a = b) : a = b.
Proof. exact (h1). Qed.
Lemma lem3888672 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : term128 _100554 b cs a) : term30 _100554 cs a.
Proof. exact (proj2 (@lem3888604 _100554 b cs a h1)). Qed.
Lemma lem3888674 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (h1 : cs a) : cs a.
Proof. exact (h1). Qed.
Lemma lem3888676 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : term125 _100554 b cs a) : term12 _100554 a b.
Proof. exact (proj1 (@lem3888609 _100554 b cs a h1)). Qed.
Lemma lem3888680 {_100554 : Type'} (a : _100554) (b : _100554) (h1 : a = b) : a = b.
Proof. exact (h1). Qed.
Lemma lem3888684 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : term125 _100554 b cs a) : term30 _100554 cs a.
Proof. exact (proj2 (@lem3888609 _100554 b cs a h1)). Qed.
Lemma lem3888686 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (h1 : cs a) : cs a.
Proof. exact (h1). Qed.
Lemma lem3888701 {_100554 : Type'} (b : _100554) : (term133 _100554 b) = (term133 _100554 b).
Proof. exact (eq_refl (term133 _100554 b)). Qed.
Lemma lem3888702 {_100554 : Type'} (a : _100554) (b : _100554) (h1 : a = b) : (term134 _100554 b a) = (term135 _100554 b).
Proof. exact (MK_COMB (@lem3888701 _100554 b) (@lem3888668 _100554 a b h1)). Qed.
Lemma lem3888703 {_100554 : Type'} (b : _100554) : (term135 _100554 b) = (term136 _100554 b).
Proof. exact (eq_refl (term135 _100554 b)). Qed.
Lemma lem3888704 {_100554 : Type'} (b : _100554) (a : _100554) : (term137 _100554 b a) = (term137 _100554 b a).
Proof. exact (eq_refl (term137 _100554 b a)). Qed.
Lemma lem3888705 {_100554 : Type'} (a : _100554) (b : _100554) : ((term134 _100554 b a) = (term135 _100554 b)) = ((term134 _100554 b a) = (term136 _100554 b)).
Proof. exact (MK_COMB (@lem3888704 _100554 b a) (@lem3888703 _100554 b)). Qed.
Lemma lem3888706 {_100554 : Type'} (a : _100554) (b : _100554) : (term134 _100554 b a) = (term12 _100554 a b).
Proof. exact (eq_refl (term134 _100554 b a)). Qed.
Lemma lem3888707 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3888708 {_100554 : Type'} (a : _100554) (b : _100554) : (term137 _100554 b a) = (term138 _100554 a b).
Proof. exact (MK_COMB (@lem3888707) (@lem3888706 _100554 a b)). Qed.
Lemma lem3888709 {_100554 : Type'} (b : _100554) : (term136 _100554 b) = (term136 _100554 b).
Proof. exact (eq_refl (term136 _100554 b)). Qed.
Lemma lem3888710 {_100554 : Type'} (a : _100554) (b : _100554) : ((term134 _100554 b a) = (term136 _100554 b)) = ((term12 _100554 a b) = (term136 _100554 b)).
Proof. exact (MK_COMB (@lem3888708 _100554 a b) (@lem3888709 _100554 b)). Qed.
Lemma lem3888711 {_100554 : Type'} (a : _100554) (b : _100554) : ((term134 _100554 b a) = (term135 _100554 b)) = ((term12 _100554 a b) = (term136 _100554 b)).
Proof. exact (TRANS (@lem3888705 _100554 a b) (@lem3888710 _100554 a b)). Qed.
Lemma lem3888712 {_100554 : Type'} (a : _100554) (b : _100554) (h1 : a = b) : (term12 _100554 a b) = (term136 _100554 b).
Proof. exact (EQ_MP (@lem3888711 _100554 a b) (@lem3888702 _100554 a b h1)). Qed.
Lemma lem3888713 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (b : _100554) (h1 : term128 _100554 b cs a) (h2 : a = b) : term136 _100554 b.
Proof. exact (EQ_MP (@lem3888712 _100554 a b h2) (@lem3888664 _100554 b cs a h1)). Qed.
Lemma lem3888741 {_100554 : Type'} (b : _100554) : (term133 _100554 b) = (term133 _100554 b).
Proof. exact (eq_refl (term133 _100554 b)). Qed.
Lemma lem3888742 {_100554 : Type'} (a : _100554) (b : _100554) (h1 : a = b) : (term134 _100554 b a) = (term135 _100554 b).
Proof. exact (MK_COMB (@lem3888741 _100554 b) (@lem3888680 _100554 a b h1)). Qed.
Lemma lem3888743 {_100554 : Type'} (b : _100554) : (term135 _100554 b) = (term136 _100554 b).
Proof. exact (eq_refl (term135 _100554 b)). Qed.
Lemma lem3888744 {_100554 : Type'} (b : _100554) (a : _100554) : (term137 _100554 b a) = (term137 _100554 b a).
Proof. exact (eq_refl (term137 _100554 b a)). Qed.
Lemma lem3888745 {_100554 : Type'} (a : _100554) (b : _100554) : ((term134 _100554 b a) = (term135 _100554 b)) = ((term134 _100554 b a) = (term136 _100554 b)).
Proof. exact (MK_COMB (@lem3888744 _100554 b a) (@lem3888743 _100554 b)). Qed.
Lemma lem3888746 {_100554 : Type'} (a : _100554) (b : _100554) : (term134 _100554 b a) = (term12 _100554 a b).
Proof. exact (eq_refl (term134 _100554 b a)). Qed.
Lemma lem3888747 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3888748 {_100554 : Type'} (a : _100554) (b : _100554) : (term137 _100554 b a) = (term138 _100554 a b).
Proof. exact (MK_COMB (@lem3888747) (@lem3888746 _100554 a b)). Qed.
Lemma lem3888749 {_100554 : Type'} (b : _100554) : (term136 _100554 b) = (term136 _100554 b).
Proof. exact (eq_refl (term136 _100554 b)). Qed.
Lemma lem3888750 {_100554 : Type'} (a : _100554) (b : _100554) : ((term134 _100554 b a) = (term136 _100554 b)) = ((term12 _100554 a b) = (term136 _100554 b)).
Proof. exact (MK_COMB (@lem3888748 _100554 a b) (@lem3888749 _100554 b)). Qed.
Lemma lem3888751 {_100554 : Type'} (a : _100554) (b : _100554) : ((term134 _100554 b a) = (term135 _100554 b)) = ((term12 _100554 a b) = (term136 _100554 b)).
Proof. exact (TRANS (@lem3888745 _100554 a b) (@lem3888750 _100554 a b)). Qed.
Lemma lem3888752 {_100554 : Type'} (a : _100554) (b : _100554) (h1 : a = b) : (term12 _100554 a b) = (term136 _100554 b).
Proof. exact (EQ_MP (@lem3888751 _100554 a b) (@lem3888742 _100554 a b h1)). Qed.
Lemma lem3888753 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (b : _100554) (h1 : term125 _100554 b cs a) (h2 : a = b) : term136 _100554 b.
Proof. exact (EQ_MP (@lem3888752 _100554 a b h2) (@lem3888676 _100554 b cs a h1)). Qed.
Lemma lem3888782 {_100554 : Type'} (x : _100554) : x = x.
Proof. exact (@lem21386 _100554 x). Qed.
Lemma lem3888783 {_100554 : Type'} (x : _100554) : x = x.
Proof. exact (@lem3888782 _100554 x). Qed.
Lemma lem3888784 {_100554 : Type'} (b : _100554) : b = b.
Proof. exact (@lem3888783 _100554 b). Qed.
Lemma lem3888785 {_100554 : Type'} (b : _100554) : term139 _100554 b.
Proof. exact (fun h0 : term136 _100554 b => @lem3888784 _100554 b). Qed.
Lemma lem3888787 (p : Prop) : (term140 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3888788 {_100554 : Type'} (b : _100554) : (term139 _100554 b) = (b = b).
Proof. exact (@lem3888787 (b = b)). Qed.
Lemma lem3888789 {_100554 : Type'} (b : _100554) : b = b.
Proof. exact (EQ_MP (@lem3888788 _100554 b) (@lem3888785 _100554 b)). Qed.
Lemma lem3888792 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3888794 {_100554 : Type'} (b : _100554) : (term136 _100554 b) = (term141 _100554 b).
Proof. exact (@lem3888792 (b = b)). Qed.
Lemma lem3888797 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (b : _100554) (h1 : term128 _100554 b cs a) (h2 : a = b) : term141 _100554 b.
Proof. exact (EQ_MP (@lem3888794 _100554 b) (@lem3888713 _100554 cs a b h1 h2)). Qed.
Lemma lem3888800 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (b : _100554) (h1 : term128 _100554 b cs a) (h2 : a = b) : False.
Proof. exact (@lem3888797 _100554 cs a b h1 h2 (@lem3888789 _100554 b)). Qed.
Lemma lem3888801 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (b : _100554) (h1 : term128 _100554 b cs a) (h2 : a = b) : term142.
Proof. exact (fun h0 : ~ False => @lem3888800 _100554 cs a b h1 h2). Qed.
Lemma lem3888803 (p : Prop) : (term140 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3888804 : term142 = False.
Proof. exact (@lem3888803 False). Qed.
Lemma lem3888821 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (h1 : cs a) : cs a.
Proof. exact (h1). Qed.
Lemma lem3888822 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (h1 : cs a) : term143 _100554 cs a.
Proof. exact (fun h0 : term30 _100554 cs a => @lem3888821 _100554 cs a h1). Qed.
Lemma lem3888824 (p : Prop) : (term140 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3888825 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) : (term143 _100554 cs a) = (cs a).
Proof. exact (@lem3888824 (cs a)). Qed.
Lemma lem3888826 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (h1 : cs a) : cs a.
Proof. exact (EQ_MP (@lem3888825 _100554 cs a) (@lem3888822 _100554 cs a h1)). Qed.
Lemma lem3888829 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3888831 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) : (term30 _100554 cs a) = (term144 _100554 cs a).
Proof. exact (@lem3888829 (cs a)). Qed.
Lemma lem3888834 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : term128 _100554 b cs a) : term144 _100554 cs a.
Proof. exact (EQ_MP (@lem3888831 _100554 cs a) (@lem3888672 _100554 b cs a h1)). Qed.
Lemma lem3888837 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : cs a) (h2 : term128 _100554 b cs a) : False.
Proof. exact (@lem3888834 _100554 b cs a h2 (@lem3888826 _100554 cs a h1)). Qed.
Lemma lem3888838 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : cs a) (h2 : term128 _100554 b cs a) : term142.
Proof. exact (fun h0 : ~ False => @lem3888837 _100554 b cs a h1 h2). Qed.
Lemma lem3888840 (p : Prop) : (term140 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3888841 : term142 = False.
Proof. exact (@lem3888840 False). Qed.
Lemma lem3888842 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : cs a) (h2 : term128 _100554 b cs a) : False.
Proof. exact (EQ_MP (@lem3888841) (@lem3888838 _100554 b cs a h1 h2)). Qed.
Lemma lem3888858 {_100554 : Type'} (x : _100554) : x = x.
Proof. exact (@lem21386 _100554 x). Qed.
Lemma lem3888859 {_100554 : Type'} (x : _100554) : x = x.
Proof. exact (@lem3888858 _100554 x). Qed.
Lemma lem3888860 {_100554 : Type'} (b : _100554) : b = b.
Proof. exact (@lem3888859 _100554 b). Qed.
Lemma lem3888861 {_100554 : Type'} (b : _100554) : term139 _100554 b.
Proof. exact (fun h0 : term136 _100554 b => @lem3888860 _100554 b). Qed.
Lemma lem3888863 (p : Prop) : (term140 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3888864 {_100554 : Type'} (b : _100554) : (term139 _100554 b) = (b = b).
Proof. exact (@lem3888863 (b = b)). Qed.
Lemma lem3888865 {_100554 : Type'} (b : _100554) : b = b.
Proof. exact (EQ_MP (@lem3888864 _100554 b) (@lem3888861 _100554 b)). Qed.
Lemma lem3888868 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3888870 {_100554 : Type'} (b : _100554) : (term136 _100554 b) = (term141 _100554 b).
Proof. exact (@lem3888868 (b = b)). Qed.
Lemma lem3888873 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (b : _100554) (h1 : term125 _100554 b cs a) (h2 : a = b) : term141 _100554 b.
Proof. exact (EQ_MP (@lem3888870 _100554 b) (@lem3888753 _100554 cs a b h1 h2)). Qed.
Lemma lem3888876 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (b : _100554) (h1 : term125 _100554 b cs a) (h2 : a = b) : False.
Proof. exact (@lem3888873 _100554 cs a b h1 h2 (@lem3888865 _100554 b)). Qed.
Lemma lem3888877 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (b : _100554) (h1 : term125 _100554 b cs a) (h2 : a = b) : term142.
Proof. exact (fun h0 : ~ False => @lem3888876 _100554 cs a b h1 h2). Qed.
Lemma lem3888879 (p : Prop) : (term140 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3888880 : term142 = False.
Proof. exact (@lem3888879 False). Qed.
Lemma lem3888897 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (h1 : cs a) : cs a.
Proof. exact (h1). Qed.
Lemma lem3888898 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (h1 : cs a) : term143 _100554 cs a.
Proof. exact (fun h0 : term30 _100554 cs a => @lem3888897 _100554 cs a h1). Qed.
Lemma lem3888900 (p : Prop) : (term140 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3888901 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) : (term143 _100554 cs a) = (cs a).
Proof. exact (@lem3888900 (cs a)). Qed.
Lemma lem3888902 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (h1 : cs a) : cs a.
Proof. exact (EQ_MP (@lem3888901 _100554 cs a) (@lem3888898 _100554 cs a h1)). Qed.
Lemma lem3888905 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3888907 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) : (term30 _100554 cs a) = (term144 _100554 cs a).
Proof. exact (@lem3888905 (cs a)). Qed.
Lemma lem3888910 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : term125 _100554 b cs a) : term144 _100554 cs a.
Proof. exact (EQ_MP (@lem3888907 _100554 cs a) (@lem3888684 _100554 b cs a h1)). Qed.
Lemma lem3888913 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : cs a) (h2 : term125 _100554 b cs a) : False.
Proof. exact (@lem3888910 _100554 b cs a h2 (@lem3888902 _100554 cs a h1)). Qed.
Lemma lem3888914 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : cs a) (h2 : term125 _100554 b cs a) : term142.
Proof. exact (fun h0 : ~ False => @lem3888913 _100554 b cs a h1 h2). Qed.
Lemma lem3888916 (p : Prop) : (term140 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3888917 : term142 = False.
Proof. exact (@lem3888916 False). Qed.
Lemma lem3888918 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : cs a) (h2 : term125 _100554 b cs a) : False.
Proof. exact (EQ_MP (@lem3888917) (@lem3888914 _100554 b cs a h1 h2)). Qed.
Lemma lem3888919 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (b : _100554) (h1 : term125 _100554 b cs a) (h2 : a = b) : False.
Proof. exact (EQ_MP (@lem3888880) (@lem3888877 _100554 cs a b h1 h2)). Qed.
Lemma lem3888920 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (b : _100554) (h1 : term128 _100554 b cs a) (h2 : a = b) : False.
Proof. exact (EQ_MP (@lem3888804) (@lem3888801 _100554 cs a b h1 h2)). Qed.
Lemma lem3888921 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : cs a) (h2 : term125 _100554 b cs a) : (cs a) = False.
Proof. exact (prop_ext (fun h3 : cs a => @lem3888918 _100554 b cs a h1 h2) (fun h3 : False => @lem3888686 _100554 cs a h1)). Qed.
Lemma lem3888922 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : cs a) (h2 : term125 _100554 b cs a) : False.
Proof. exact (EQ_MP (@lem3888921 _100554 b cs a h1 h2) (@lem3888686 _100554 cs a h1)). Qed.
Lemma lem3888923 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (b : _100554) (h1 : term125 _100554 b cs a) (h2 : a = b) : (a = b) = False.
Proof. exact (prop_ext (fun h3 : a = b => @lem3888919 _100554 cs a b h1 h2) (fun h3 : False => @lem3888680 _100554 a b h2)). Qed.
Lemma lem3888924 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (b : _100554) (h1 : term125 _100554 b cs a) (h2 : a = b) : False.
Proof. exact (EQ_MP (@lem3888923 _100554 cs a b h1 h2) (@lem3888680 _100554 a b h2)). Qed.
Lemma lem3888925 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : cs a) (h2 : term128 _100554 b cs a) : (cs a) = False.
Proof. exact (prop_ext (fun h3 : cs a => @lem3888842 _100554 b cs a h1 h2) (fun h3 : False => @lem3888674 _100554 cs a h1)). Qed.
Lemma lem3888926 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : cs a) (h2 : term128 _100554 b cs a) : False.
Proof. exact (EQ_MP (@lem3888925 _100554 b cs a h1 h2) (@lem3888674 _100554 cs a h1)). Qed.
Lemma lem3888927 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (b : _100554) (h1 : term128 _100554 b cs a) (h2 : a = b) : (a = b) = False.
Proof. exact (prop_ext (fun h3 : a = b => @lem3888920 _100554 cs a b h1 h2) (fun h3 : False => @lem3888668 _100554 a b h2)). Qed.
Lemma lem3888928 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (b : _100554) (h1 : term128 _100554 b cs a) (h2 : a = b) : False.
Proof. exact (EQ_MP (@lem3888927 _100554 cs a b h1 h2) (@lem3888668 _100554 a b h2)). Qed.
Lemma lem3888929 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : cs a) (h2 : term125 _100554 b cs a) : (cs a) = False.
Proof. exact (prop_ext (fun h3 : cs a => @lem3888922 _100554 b cs a h1 h2) (fun h3 : False => @lem3888662 _100554 cs a h1)). Qed.
Lemma lem3888930 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : cs a) (h2 : term125 _100554 b cs a) : False.
Proof. exact (EQ_MP (@lem3888929 _100554 b cs a h1 h2) (@lem3888662 _100554 cs a h1)). Qed.
Lemma lem3888931 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (b : _100554) (h1 : term125 _100554 b cs a) (h2 : a = b) : (a = b) = False.
Proof. exact (prop_ext (fun h3 : a = b => @lem3888924 _100554 cs a b h1 h2) (fun h3 : False => @lem3888650 _100554 a b h2)). Qed.
Lemma lem3888932 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (b : _100554) (h1 : term125 _100554 b cs a) (h2 : a = b) : False.
Proof. exact (EQ_MP (@lem3888931 _100554 cs a b h1 h2) (@lem3888650 _100554 a b h2)). Qed.
Lemma lem3888933 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : cs a) (h2 : term128 _100554 b cs a) : (cs a) = False.
Proof. exact (prop_ext (fun h3 : cs a => @lem3888926 _100554 b cs a h1 h2) (fun h3 : False => @lem3888638 _100554 cs a h1)). Qed.
Lemma lem3888934 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : cs a) (h2 : term128 _100554 b cs a) : False.
Proof. exact (EQ_MP (@lem3888933 _100554 b cs a h1 h2) (@lem3888638 _100554 cs a h1)). Qed.
Lemma lem3888935 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (b : _100554) (h1 : term128 _100554 b cs a) (h2 : a = b) : (a = b) = False.
Proof. exact (prop_ext (fun h3 : a = b => @lem3888928 _100554 cs a b h1 h2) (fun h3 : False => @lem3888626 _100554 a b h2)). Qed.
Lemma lem3888936 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (b : _100554) (h1 : term128 _100554 b cs a) (h2 : a = b) : False.
Proof. exact (EQ_MP (@lem3888935 _100554 cs a b h1 h2) (@lem3888626 _100554 a b h2)). Qed.
Lemma lem3888937 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : cs a) (h2 : term125 _100554 b cs a) : (cs a) = False.
Proof. exact (prop_ext (fun h3 : cs a => @lem3888930 _100554 b cs a h1 h2) (fun h3 : False => @lem3888662 _100554 cs a h1)). Qed.
Lemma lem3888938 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : cs a) (h2 : term125 _100554 b cs a) : False.
Proof. exact (EQ_MP (@lem3888937 _100554 b cs a h1 h2) (@lem3888662 _100554 cs a h1)). Qed.
Lemma lem3888939 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (b : _100554) (h1 : term125 _100554 b cs a) (h2 : a = b) : (a = b) = False.
Proof. exact (prop_ext (fun h3 : a = b => @lem3888932 _100554 cs a b h1 h2) (fun h3 : False => @lem3888650 _100554 a b h2)). Qed.
Lemma lem3888940 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (b : _100554) (h1 : term125 _100554 b cs a) (h2 : a = b) : False.
Proof. exact (EQ_MP (@lem3888939 _100554 cs a b h1 h2) (@lem3888650 _100554 a b h2)). Qed.
Lemma lem3888941 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : cs a) (h2 : term128 _100554 b cs a) : (cs a) = False.
Proof. exact (prop_ext (fun h3 : cs a => @lem3888934 _100554 b cs a h1 h2) (fun h3 : False => @lem3888638 _100554 cs a h1)). Qed.
Lemma lem3888942 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : cs a) (h2 : term128 _100554 b cs a) : False.
Proof. exact (EQ_MP (@lem3888941 _100554 b cs a h1 h2) (@lem3888638 _100554 cs a h1)). Qed.
Lemma lem3888943 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (b : _100554) (h1 : term128 _100554 b cs a) (h2 : a = b) : (a = b) = False.
Proof. exact (prop_ext (fun h3 : a = b => @lem3888936 _100554 cs a b h1 h2) (fun h3 : False => @lem3888626 _100554 a b h2)). Qed.
Lemma lem3888944 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (b : _100554) (h1 : term128 _100554 b cs a) (h2 : a = b) : False.
Proof. exact (EQ_MP (@lem3888943 _100554 cs a b h1 h2) (@lem3888626 _100554 a b h2)). Qed.
Lemma lem3888945 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : term125 _100554 b cs a) : False.
Proof. exact (or_elim (@lem3888610 _100554 b cs a h1) (fun h0 : a = b => @lem3888940 _100554 cs a b h1 h0) (fun h0 : cs a => @lem3888938 _100554 b cs a h0 h1)). Qed.
Lemma lem3888946 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : term128 _100554 b cs a) : False.
Proof. exact (or_elim (@lem3888603 _100554 b cs a h1) (fun h0 : a = b => @lem3888944 _100554 cs a b h1 h0) (fun h0 : cs a => @lem3888942 _100554 b cs a h0 h1)). Qed.
Lemma lem3888947 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : term115 _100554 b cs a) : False.
Proof. exact (or_elim (@lem3888600 _100554 b cs a h1) (fun h0 : term128 _100554 b cs a => @lem3888946 _100554 b cs a h0) (fun h0 : term125 _100554 b cs a => @lem3888945 _100554 b cs a h0)). Qed.
Lemma lem3888948 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : term115 _100554 b cs a) : (term115 _100554 b cs a) = False.
Proof. exact (prop_ext (fun h2 : term115 _100554 b cs a => @lem3888947 _100554 b cs a h1) (fun h2 : False => @lem3888492 _100554 b cs a h1)). Qed.
Lemma lem3888949 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (h1 : term115 _100554 b cs a) : False.
Proof. exact (EQ_MP (@lem3888948 _100554 b cs a h1) (@lem3888492 _100554 b cs a h1)). Qed.
Lemma lem3888950 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) : term114 _100554 b cs a.
Proof. exact (fun h0 : term115 _100554 b cs a => @lem3888949 _100554 b cs a h0). Qed.
Lemma lem3888951 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) : (term22 _100554 b cs a) = (term84 _100554 b cs a).
Proof. exact (EQ_MP (@lem3888491 _100554 b cs a) (@lem3888950 _100554 b cs a)). Qed.
Lemma lem3888956 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) : term88 _100554 cs a.
Proof. exact (fun b : _100554 => @lem3888951 _100554 b cs a). Qed.
Lemma lem3888961 {_100554 : Type'} (a : _100554) : term92 _100554 a.
Proof. exact (fun cs : _100554 -> Prop => @lem3888956 _100554 cs a). Qed.
Lemma lem3888966 {_100554 : Type'} : term95 _100554.
Proof. exact (fun a : _100554 => @lem3888961 _100554 a). Qed.
Lemma lem3888967 {_100554 : Type'} : term62 _100554.
Proof. exact (EQ_MP (@lem3888487 _100554) (@lem3888966 _100554)). Qed.
Lemma lem3888968 {_100554 : Type'} (P : Prop) : term145 _100554 P.
Proof. exact (@lem3888967 _100554 P). Qed.
Lemma lem3888969 {_100554 : Type'} (P : Prop) : (term145 _100554 P) = (term58 _100554 P).
Proof. exact (eq_refl (term145 _100554 P)). Qed.
Lemma lem3888970 {_100554 : Type'} (P : Prop) : term58 _100554 P.
Proof. exact (EQ_MP (@lem3888969 _100554 P) (@lem3888968 _100554 P)). Qed.
Lemma lem3888971 {_100554 : Type'} (P : Prop) (a : _100554) : term146 _100554 P a.
Proof. exact (@lem3888970 _100554 P a). Qed.
Lemma lem3888972 {_100554 : Type'} (a : _100554) (P : Prop) : (term146 _100554 P a) = (term54 _100554 a P).
Proof. exact (eq_refl (term146 _100554 P a)). Qed.
Lemma lem3888973 {_100554 : Type'} (a : _100554) (P : Prop) : term54 _100554 a P.
Proof. exact (EQ_MP (@lem3888972 _100554 a P) (@lem3888971 _100554 P a)). Qed.
Lemma lem3888974 {_100554 : Type'} (a : _100554) (P : Prop) (cs : _100554 -> Prop) : term147 _100554 a P cs.
Proof. exact (@lem3888973 _100554 a P cs). Qed.
Lemma lem3888975 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (P : Prop) : (term147 _100554 a P cs) = (term50 _100554 cs a P).
Proof. exact (eq_refl (term147 _100554 a P cs)). Qed.
Lemma lem3888976 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (P : Prop) : term50 _100554 cs a P.
Proof. exact (EQ_MP (@lem3888975 _100554 cs a P) (@lem3888974 _100554 a P cs)). Qed.
Lemma lem3888977 {_100554 : Type'} (cs : _100554 -> Prop) (a : _100554) (P : Prop) (b : _100554) : term148 _100554 cs a P b.
Proof. exact (@lem3888976 _100554 cs a P b). Qed.
Lemma lem3888978 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) : (term148 _100554 cs a P b) = (term41 _100554 b cs a P).
Proof. exact (eq_refl (term148 _100554 cs a P b)). Qed.
Lemma lem3888979 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) : term41 _100554 b cs a P.
Proof. exact (EQ_MP (@lem3888978 _100554 b cs a P) (@lem3888977 _100554 cs a P b)). Qed.
Lemma lem3888981 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) : term41 _100554 b cs a P.
Proof. exact (@lem3888202 _100554 b cs a P (@lem3888979 _100554 b cs a P)). Qed.
Lemma lem3888982 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) (h1 : term42 _100554 b cs a P) : False.
Proof. exact (@lem3888981 _100554 b cs a P (@lem3888186 _100554 b cs a P h1)). Qed.
Lemma lem3888983 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) (h1 : term42 _100554 b cs a P) : (term42 _100554 b cs a P) = False.
Proof. exact (prop_ext (fun h2 : term42 _100554 b cs a P => @lem3888982 _100554 b cs a P h1) (fun h2 : False => @lem3888186 _100554 b cs a P h1)). Qed.
Lemma lem3888984 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) (h1 : term42 _100554 b cs a P) : False.
Proof. exact (EQ_MP (@lem3888983 _100554 b cs a P h1) (@lem3888186 _100554 b cs a P h1)). Qed.
Lemma lem3888985 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) : term41 _100554 b cs a P.
Proof. exact (fun h0 : term42 _100554 b cs a P => @lem3888984 _100554 b cs a P h0). Qed.
Lemma lem3888986 {_100554 : Type'} (b : _100554) (cs : _100554 -> Prop) (a : _100554) (P : Prop) : (term26 _100554 b cs a P) = (term36 _100554 b cs a P).
Proof. exact (EQ_MP (@lem3888185 _100554 b cs a P) (@lem3888985 _100554 b cs a P)). Qed.
Lemma lem3888988 {_100554 : Type'} (b : _100554) (a : _100554) (cs : _100554 -> Prop) (P : Prop) : term39 _100554 b a cs P.
Proof. exact (EQ_MP (@lem3888181 _100554 b a cs P) (@lem3888986 _100554 b cs a P)). Qed.
