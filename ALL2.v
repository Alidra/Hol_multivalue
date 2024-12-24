Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ALL2_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1073523_spec.
Require Import thm1094865_spec.
Require Import thm1094866_spec.
Require Import thm1095388_spec.
Require Import thm1095389_spec.
Require Import thm1104043_spec.
Require Import thm1104044_spec.
Require Import thm1104055_spec.
Require Import thm1104056_spec.
Require Import thm12653_spec.
Require Import thm15249_spec.
Require Import thm1842_spec.
Require Import thm1856_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm82_spec.
Lemma lem1104061 {A : Type'} (a0' : A) : term0 A a0'.
Proof. exact (@lem1073523 A a0'). Qed.
Lemma lem1104062 {A : Type'} (a0' : A) : (term0 A a0') = (term1 A a0').
Proof. exact (eq_refl (term0 A a0')). Qed.
Lemma lem1104063 {A : Type'} (a0' : A) : term1 A a0'.
Proof. exact (EQ_MP (@lem1104062 A a0') (@lem1104061 A a0')). Qed.
Lemma lem1104064 {A : Type'} (a0' : A) (a1' : list A) : term2 A a0' a1'.
Proof. exact (@lem1104063 A a0' a1'). Qed.
Lemma lem1104065 {A : Type'} (a0' : A) (a1' : list A) : (term2 A a0' a1') = (term3 A a0' a1').
Proof. exact (eq_refl (term2 A a0' a1')). Qed.
Lemma lem1104066 {A : Type'} (a0' : A) (a1' : list A) : term3 A a0' a1'.
Proof. exact (EQ_MP (@lem1104065 A a0' a1') (@lem1104064 A a0' a1')). Qed.
Lemma lem1104070 {A : Type'} (a0' : A) (a1' : list A) (h1 : (@nil A) = (@cons A a0' a1')) : (@nil A) = (@cons A a0' a1').
Proof. exact (h1). Qed.
Lemma lem1104071 {A : Type'} (a0' : A) (a1' : list A) (h1 : (@nil A) = (@cons A a0' a1')) : (@cons A a0' a1') = (@nil A).
Proof. exact (SYM (@lem1104070 A a0' a1' h1)). Qed.
Lemma lem1104072 {A : Type'} (a0' : A) (a1' : list A) (h1 : (@cons A a0' a1') = (@nil A)) : (@cons A a0' a1') = (@nil A).
Proof. exact (h1). Qed.
Lemma lem1104073 {A : Type'} (a0' : A) (a1' : list A) (h1 : (@cons A a0' a1') = (@nil A)) : (@nil A) = (@cons A a0' a1').
Proof. exact (SYM (@lem1104072 A a0' a1' h1)). Qed.
Lemma lem1104074 {A : Type'} (a0' : A) (a1' : list A) : ((@nil A) = (@cons A a0' a1')) = ((@cons A a0' a1') = (@nil A)).
Proof. exact (prop_ext (fun h1 : (@nil A) = (@cons A a0' a1') => @lem1104071 A a0' a1' h1) (fun h1 : (@cons A a0' a1') = (@nil A) => @lem1104073 A a0' a1' h1)). Qed.
Lemma lem1104075 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1104076 {A : Type'} (a0' : A) (a1' : list A) : (term3 A a0' a1') = (term4 A a0' a1').
Proof. exact (MK_COMB (@lem1104075) (@lem1104074 A a0' a1')). Qed.
Lemma lem1104077 {A : Type'} (a0' : A) (a1' : list A) : term4 A a0' a1'.
Proof. exact (EQ_MP (@lem1104076 A a0' a1') (@lem1104066 A a0' a1')). Qed.
Lemma lem1104078 {A : Type'} (a0' : A) (a1' : list A) : term5 A a0' a1'.
Proof. exact (@lem82 ((@cons A a0' a1') = (@nil A))). Qed.
Lemma lem1104083 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem1104084 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) : ((@ALL2 _25471 _25470 P (@nil _25471) (@nil _25470)) = True) = (@ALL2 _25471 _25470 P (@nil _25471) (@nil _25470)).
Proof. exact (@lem1104083 (@ALL2 _25471 _25470 P (@nil _25471) (@nil _25470))). Qed.
Lemma lem1104086 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (l2 : list _25416) : (@ALL2 _25409 _25416 P (@nil _25409) l2) = (l2 = (@nil _25416)).
Proof. exact (EQ_MP (@lem1104044 _25409 _25416 P l2) (@lem1104043 _25409 _25416 P l2)). Qed.
Lemma lem1104087 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) (l2 : list _25470) : (@ALL2 _25471 _25470 P (@nil _25471) l2) = (l2 = (@nil _25470)).
Proof. exact (@lem1104086 _25471 _25470 P l2). Qed.
Lemma lem1104088 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) : (@ALL2 _25471 _25470 P (@nil _25471) (@nil _25470)) = ((@nil _25470) = (@nil _25470)).
Proof. exact (@lem1104087 _25470 _25471 P (@nil _25470)). Qed.
Lemma lem1104090 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1104091 {_25470 : Type'} (x : list _25470) : (x = x) = True.
Proof. exact (@lem1104090 (list _25470) x). Qed.
Lemma lem1104092 {_25470 : Type'} : ((@nil _25470) = (@nil _25470)) = True.
Proof. exact (@lem1104091 _25470 (@nil _25470)). Qed.
Lemma lem1104093 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) : (@ALL2 _25471 _25470 P (@nil _25471) (@nil _25470)) = True.
Proof. exact (TRANS (@lem1104088 _25470 _25471 P) (@lem1104092 _25470)). Qed.
Lemma lem1104094 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) : ((@ALL2 _25471 _25470 P (@nil _25471) (@nil _25470)) = True) = True.
Proof. exact (TRANS (@lem1104084 _25470 _25471 P) (@lem1104093 _25470 _25471 P)). Qed.
Lemma lem1104095 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1104096 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) : (term6 _25470 _25471 P) = (and True).
Proof. exact (MK_COMB (@lem1104095) (@lem1104094 _25470 _25471 P)). Qed.
Lemma lem1104100 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem1104101 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) (h1' : _25471) (t1 : list _25471) : ((term7 _25470 _25471 P h1' t1) = False) = (term8 _25470 _25471 P h1' t1).
Proof. exact (@lem1104100 (term7 _25470 _25471 P h1' t1)). Qed.
Lemma lem1104103 {_25409 _25416 : Type'} (h1' : _25409) (P : type1413 _25409 _25416) (t1 : list _25409) (l2 : list _25416) : (term9 _25409 _25416 P h1' t1 l2) = (term10 _25409 _25416 h1' P t1 l2).
Proof. exact (EQ_MP (@lem1104056 _25409 _25416 h1' P t1 l2) (@lem1104055 _25409 _25416 h1' P t1 l2)). Qed.
Lemma lem1104104 {_25470 _25471 : Type'} (h1' : _25471) (P : type1470 _25470 _25471) (t1 : list _25471) (l2 : list _25470) : (term11 _25470 _25471 P h1' t1 l2) = (term12 _25470 _25471 h1' P t1 l2).
Proof. exact (@lem1104103 _25471 _25470 h1' P t1 l2). Qed.
Lemma lem1104105 {_25470 _25471 : Type'} (h1' : _25471) (P : type1470 _25470 _25471) (t1 : list _25471) : (term7 _25470 _25471 P h1' t1) = (term13 _25470 _25471 h1' P t1).
Proof. exact (@lem1104104 _25470 _25471 h1' P t1 (@nil _25470)). Qed.
Lemma lem1104107 {_2975 _2982 : Type'} (x : _2982) (z : _2975) (y : _2975) : (term14 _2975 _2982 x y z) = y.
Proof. exact (EQ_MP (@lem15249 _2975 _2982 x z y) (@lem0)). Qed.
Lemma lem1104108 {_25470 : Type'} (x : list _25470) (z : Prop) (y : Prop) : (term15 _25470 x y z) = y.
Proof. exact (@lem1104107 Prop (list _25470) x z y). Qed.
Lemma lem1104109 {_25470 _25471 : Type'} (h1' : _25471) (P : type1470 _25470 _25471) (t1 : list _25471) : (term13 _25470 _25471 h1' P t1) = False.
Proof. exact (@lem1104108 _25470 (@nil _25470) (term16 _25470 _25471 h1' P t1) False). Qed.
Lemma lem1104110 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) (h1' : _25471) (t1 : list _25471) : (term7 _25470 _25471 P h1' t1) = False.
Proof. exact (TRANS (@lem1104105 _25470 _25471 h1' P t1) (@lem1104109 _25470 _25471 h1' P t1)). Qed.
Lemma lem1104111 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1104112 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) (h1' : _25471) (t1 : list _25471) : (term8 _25470 _25471 P h1' t1) = (~ False).
Proof. exact (MK_COMB (@lem1104111) (@lem1104110 _25470 _25471 P h1' t1)). Qed.
Lemma lem1104114 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1104115 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) (h1' : _25471) (t1 : list _25471) : (term8 _25470 _25471 P h1' t1) = True.
Proof. exact (TRANS (@lem1104112 _25470 _25471 P h1' t1) (@lem1104114)). Qed.
Lemma lem1104116 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) (h1' : _25471) (t1 : list _25471) : ((term7 _25470 _25471 P h1' t1) = False) = True.
Proof. exact (TRANS (@lem1104101 _25470 _25471 P h1' t1) (@lem1104115 _25470 _25471 P h1' t1)). Qed.
Lemma lem1104117 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1104118 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) (h1' : _25471) (t1 : list _25471) : (term17 _25470 _25471 P h1' t1) = (and True).
Proof. exact (MK_COMB (@lem1104117) (@lem1104116 _25470 _25471 P h1' t1)). Qed.
Lemma lem1104122 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem1104123 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) (h2' : _25470) (t2 : list _25470) : ((term18 _25470 _25471 P h2' t2) = False) = (term19 _25470 _25471 P h2' t2).
Proof. exact (@lem1104122 (term18 _25470 _25471 P h2' t2)). Qed.
Lemma lem1104125 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (l2 : list _25416) : (@ALL2 _25409 _25416 P (@nil _25409) l2) = (l2 = (@nil _25416)).
Proof. exact (EQ_MP (@lem1104044 _25409 _25416 P l2) (@lem1104043 _25409 _25416 P l2)). Qed.
Lemma lem1104126 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) (l2 : list _25470) : (@ALL2 _25471 _25470 P (@nil _25471) l2) = (l2 = (@nil _25470)).
Proof. exact (@lem1104125 _25471 _25470 P l2). Qed.
Lemma lem1104127 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) (h2' : _25470) (t2 : list _25470) : (term18 _25470 _25471 P h2' t2) = ((@cons _25470 h2' t2) = (@nil _25470)).
Proof. exact (@lem1104126 _25470 _25471 P (@cons _25470 h2' t2)). Qed.
Lemma lem1104129 {A : Type'} (a0' : A) (a1' : list A) : ((@cons A a0' a1') = (@nil A)) = False.
Proof. exact (@lem1104078 A a0' a1' (@lem1104077 A a0' a1')). Qed.
Lemma lem1104130 {_25470 : Type'} (a0' : _25470) (a1' : list _25470) : ((@cons _25470 a0' a1') = (@nil _25470)) = False.
Proof. exact (@lem1104129 _25470 a0' a1'). Qed.
Lemma lem1104131 {_25470 : Type'} (h2' : _25470) (t2 : list _25470) : ((@cons _25470 h2' t2) = (@nil _25470)) = False.
Proof. exact (@lem1104130 _25470 h2' t2). Qed.
Lemma lem1104132 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) (h2' : _25470) (t2 : list _25470) : (term18 _25470 _25471 P h2' t2) = False.
Proof. exact (TRANS (@lem1104127 _25470 _25471 P h2' t2) (@lem1104131 _25470 h2' t2)). Qed.
Lemma lem1104133 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1104134 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) (h2' : _25470) (t2 : list _25470) : (term19 _25470 _25471 P h2' t2) = (~ False).
Proof. exact (MK_COMB (@lem1104133) (@lem1104132 _25470 _25471 P h2' t2)). Qed.
Lemma lem1104136 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1104137 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) (h2' : _25470) (t2 : list _25470) : (term19 _25470 _25471 P h2' t2) = True.
Proof. exact (TRANS (@lem1104134 _25470 _25471 P h2' t2) (@lem1104136)). Qed.
Lemma lem1104138 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) (h2' : _25470) (t2 : list _25470) : ((term18 _25470 _25471 P h2' t2) = False) = True.
Proof. exact (TRANS (@lem1104123 _25470 _25471 P h2' t2) (@lem1104137 _25470 _25471 P h2' t2)). Qed.
Lemma lem1104139 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1104140 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) (h2' : _25470) (t2 : list _25470) : (term20 _25470 _25471 P h2' t2) = (and True).
Proof. exact (MK_COMB (@lem1104139) (@lem1104138 _25470 _25471 P h2' t2)). Qed.
Lemma lem1104144 {_25409 _25416 : Type'} (h1' : _25409) (P : type1413 _25409 _25416) (t1 : list _25409) (l2 : list _25416) : (term9 _25409 _25416 P h1' t1 l2) = (term10 _25409 _25416 h1' P t1 l2).
Proof. exact (EQ_MP (@lem1104056 _25409 _25416 h1' P t1 l2) (@lem1104055 _25409 _25416 h1' P t1 l2)). Qed.
Lemma lem1104145 {_25470 _25471 : Type'} (h1' : _25471) (P : type1470 _25470 _25471) (t1 : list _25471) (l2 : list _25470) : (term11 _25470 _25471 P h1' t1 l2) = (term12 _25470 _25471 h1' P t1 l2).
Proof. exact (@lem1104144 _25471 _25470 h1' P t1 l2). Qed.
Lemma lem1104146 {_25470 _25471 : Type'} (h1' : _25471) (P : type1470 _25470 _25471) (t1 : list _25471) (h2' : _25470) (t2 : list _25470) : (term21 _25470 _25471 P h1' t1 h2' t2) = (term22 _25470 _25471 h1' P t1 h2' t2).
Proof. exact (@lem1104145 _25470 _25471 h1' P t1 (@cons _25470 h2' t2)). Qed.
Lemma lem1104150 {A : Type'} (a0' : A) (a1' : list A) : ((@cons A a0' a1') = (@nil A)) = False.
Proof. exact (@lem1104078 A a0' a1' (@lem1104077 A a0' a1')). Qed.
Lemma lem1104151 {_25470 : Type'} (a0' : _25470) (a1' : list _25470) : ((@cons _25470 a0' a1') = (@nil _25470)) = False.
Proof. exact (@lem1104150 _25470 a0' a1'). Qed.
Lemma lem1104152 {_25470 : Type'} (h2' : _25470) (t2 : list _25470) : ((@cons _25470 h2' t2) = (@nil _25470)) = False.
Proof. exact (@lem1104151 _25470 h2' t2). Qed.
Lemma lem1104153 : (@COND Prop) = (@COND Prop).
Proof. exact (eq_refl (@COND Prop)). Qed.
Lemma lem1104154 {_25470 : Type'} (h2' : _25470) (t2 : list _25470) : (term23 _25470 h2' t2) = (@COND Prop False).
Proof. exact (MK_COMB (@lem1104153) (@lem1104152 _25470 h2' t2)). Qed.
Lemma lem1104155 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem1104156 {_25470 : Type'} (h2' : _25470) (t2 : list _25470) : (term24 _25470 h2' t2) = (@COND Prop False False).
Proof. exact (MK_COMB (@lem1104154 _25470 h2' t2) (@lem1104155)). Qed.
Lemma lem1104160 {A : Type'} (t : list A) (h : A) : (term25 A h t) = h.
Proof. exact (EQ_MP (@lem1094866 A t h) (@lem1094865 A t h)). Qed.
Lemma lem1104161 {_25470 : Type'} (t : list _25470) (h : _25470) : (term25 _25470 h t) = h.
Proof. exact (@lem1104160 _25470 t h). Qed.
Lemma lem1104162 {_25470 : Type'} (t2 : list _25470) (h2' : _25470) : (term25 _25470 h2' t2) = h2'.
Proof. exact (@lem1104161 _25470 t2 h2'). Qed.
Lemma lem1104163 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) (h1' : _25471) : (P h1') = (P h1').
Proof. exact (eq_refl (P h1')). Qed.
Lemma lem1104164 {_25470 _25471 : Type'} (t2 : list _25470) (P : type1470 _25470 _25471) (h1' : _25471) (h2' : _25470) : (term26 _25470 _25471 P h1' h2' t2) = (P h1' h2').
Proof. exact (MK_COMB (@lem1104163 _25470 _25471 P h1') (@lem1104162 _25470 t2 h2')). Qed.
Lemma lem1104165 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1104166 {_25470 _25471 : Type'} (t2 : list _25470) (P : type1470 _25470 _25471) (h1' : _25471) (h2' : _25470) : (term27 _25470 _25471 P h1' h2' t2) = (term28 _25470 _25471 P h1' h2').
Proof. exact (MK_COMB (@lem1104165) (@lem1104164 _25470 _25471 t2 P h1' h2')). Qed.
Lemma lem1104168 {A : Type'} (h : A) (t : list A) : (term29 A h t) = t.
Proof. exact (EQ_MP (@lem1095389 A h t) (@lem1095388 A h t)). Qed.
Lemma lem1104169 {_25470 : Type'} (h : _25470) (t : list _25470) : (term29 _25470 h t) = t.
Proof. exact (@lem1104168 _25470 h t). Qed.
Lemma lem1104170 {_25470 : Type'} (h2' : _25470) (t2 : list _25470) : (term29 _25470 h2' t2) = t2.
Proof. exact (@lem1104169 _25470 h2' t2). Qed.
Lemma lem1104171 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) (t1 : list _25471) : (@ALL2 _25471 _25470 P t1) = (@ALL2 _25471 _25470 P t1).
Proof. exact (eq_refl (@ALL2 _25471 _25470 P t1)). Qed.
Lemma lem1104172 {_25470 _25471 : Type'} (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : (term30 _25470 _25471 P t1 h2' t2) = (@ALL2 _25471 _25470 P t1 t2).
Proof. exact (MK_COMB (@lem1104171 _25470 _25471 P t1) (@lem1104170 _25470 h2' t2)). Qed.
Lemma lem1104173 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : (term31 _25470 _25471 h1' P t1 h2' t2) = (term32 _25470 _25471 h1' h2' P t1 t2).
Proof. exact (MK_COMB (@lem1104166 _25470 _25471 t2 P h1' h2') (@lem1104172 _25470 _25471 h2' P t1 t2)). Qed.
Lemma lem1104176 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : (term22 _25470 _25471 h1' P t1 h2' t2) = (term33 _25470 _25471 h1' h2' P t1 t2).
Proof. exact (MK_COMB (@lem1104156 _25470 h2' t2) (@lem1104173 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1104178 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1104179 (t1 : Prop) (t2 : Prop) : (@COND Prop False t1 t2) = t2.
Proof. exact (@lem1104178 Prop t1 t2). Qed.
Lemma lem1104180 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : (term33 _25470 _25471 h1' h2' P t1 t2) = (term32 _25470 _25471 h1' h2' P t1 t2).
Proof. exact (@lem1104179 False (term32 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1104183 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : (term22 _25470 _25471 h1' P t1 h2' t2) = (term32 _25470 _25471 h1' h2' P t1 t2).
Proof. exact (TRANS (@lem1104176 _25470 _25471 h1' h2' P t1 t2) (@lem1104180 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1104184 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : (term21 _25470 _25471 P h1' t1 h2' t2) = (term32 _25470 _25471 h1' h2' P t1 t2).
Proof. exact (TRANS (@lem1104146 _25470 _25471 h1' P t1 h2' t2) (@lem1104183 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1104185 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1104186 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : (term34 _25470 _25471 P h1' t1 h2' t2) = (term35 _25470 _25471 h1' h2' P t1 t2).
Proof. exact (MK_COMB (@lem1104185) (@lem1104184 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1104189 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : (term32 _25470 _25471 h1' h2' P t1 t2) = (term32 _25470 _25471 h1' h2' P t1 t2).
Proof. exact (eq_refl (term32 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1104190 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : ((term21 _25470 _25471 P h1' t1 h2' t2) = (term32 _25470 _25471 h1' h2' P t1 t2)) = ((term32 _25470 _25471 h1' h2' P t1 t2) = (term32 _25470 _25471 h1' h2' P t1 t2)).
Proof. exact (MK_COMB (@lem1104186 _25470 _25471 h1' h2' P t1 t2) (@lem1104189 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1104192 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1104193 (x : Prop) : (x = x) = True.
Proof. exact (@lem1104192 Prop x). Qed.
Lemma lem1104194 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : ((term32 _25470 _25471 h1' h2' P t1 t2) = (term32 _25470 _25471 h1' h2' P t1 t2)) = True.
Proof. exact (@lem1104193 (term32 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1104195 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : ((term21 _25470 _25471 P h1' t1 h2' t2) = (term32 _25470 _25471 h1' h2' P t1 t2)) = True.
Proof. exact (TRANS (@lem1104190 _25470 _25471 h1' h2' P t1 t2) (@lem1104194 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1104196 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : (term36 _25470 _25471 h1' h2' P t1 t2) = (True /\ True).
Proof. exact (MK_COMB (@lem1104140 _25470 _25471 P h2' t2) (@lem1104195 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1104198 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1104199 : (True /\ True) = True.
Proof. exact (@lem1104198 True). Qed.
Lemma lem1104200 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : (term36 _25470 _25471 h1' h2' P t1 t2) = True.
Proof. exact (TRANS (@lem1104196 _25470 _25471 h1' h2' P t1 t2) (@lem1104199)). Qed.
Lemma lem1104201 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : (term37 _25470 _25471 h1' h2' P t1 t2) = (True /\ True).
Proof. exact (MK_COMB (@lem1104118 _25470 _25471 P h1' t1) (@lem1104200 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1104203 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1104204 : (True /\ True) = True.
Proof. exact (@lem1104203 True). Qed.
Lemma lem1104205 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : (term37 _25470 _25471 h1' h2' P t1 t2) = True.
Proof. exact (TRANS (@lem1104201 _25470 _25471 h1' h2' P t1 t2) (@lem1104204)). Qed.
Lemma lem1104206 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : (term38 _25470 _25471 h1' h2' P t1 t2) = (True /\ True).
Proof. exact (MK_COMB (@lem1104096 _25470 _25471 P) (@lem1104205 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1104208 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1104209 : (True /\ True) = True.
Proof. exact (@lem1104208 True). Qed.
Lemma lem1104210 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : (term38 _25470 _25471 h1' h2' P t1 t2) = True.
Proof. exact (TRANS (@lem1104206 _25470 _25471 h1' h2' P t1 t2) (@lem1104209)). Qed.
Lemma lem1104211 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : True = (term38 _25470 _25471 h1' h2' P t1 t2).
Proof. exact (SYM (@lem1104210 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1104212 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : term38 _25470 _25471 h1' h2' P t1 t2.
Proof. exact (EQ_MP (@lem1104211 _25470 _25471 h1' h2' P t1 t2) (@lem0)). Qed.
