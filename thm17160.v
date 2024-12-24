Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm17160_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem17054 (p : Prop) : term0 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem17055 (p : Prop) : (term0 p) = (term1 p).
Proof. exact (eq_refl (term0 p)). Qed.
Lemma lem17056 (p : Prop) : term1 p.
Proof. exact (EQ_MP (@lem17055 p) (@lem17054 p)). Qed.
Lemma lem17057 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem17058 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem17067 (q : Prop) : (term2 q) = (term2 q).
Proof. exact (eq_refl (term2 q)). Qed.
Lemma lem17068 (q : Prop) (p : Prop) (h1 : p = True) : (term3 q p) = (term4 q).
Proof. exact (MK_COMB (@lem17067 q) (@lem17057 p h1)). Qed.
Lemma lem17069 (q : Prop) : (term4 q) = ((term5 q) = (term6 q)).
Proof. exact (eq_refl (term4 q)). Qed.
Lemma lem17070 (q : Prop) (p : Prop) : (term7 q p) = (term7 q p).
Proof. exact (eq_refl (term7 q p)). Qed.
Lemma lem17071 (p : Prop) (q : Prop) : ((term3 q p) = (term4 q)) = ((term3 q p) = ((term5 q) = (term6 q))).
Proof. exact (MK_COMB (@lem17070 q p) (@lem17069 q)). Qed.
Lemma lem17072 (p : Prop) (q : Prop) : (term3 q p) = ((term8 p q) = (term9 p q)).
Proof. exact (eq_refl (term3 q p)). Qed.
Lemma lem17073 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem17074 (p : Prop) (q : Prop) : (term7 q p) = (term10 p q).
Proof. exact (MK_COMB (@lem17073) (@lem17072 p q)). Qed.
Lemma lem17075 (q : Prop) : ((term5 q) = (term6 q)) = ((term5 q) = (term6 q)).
Proof. exact (eq_refl ((term5 q) = (term6 q))). Qed.
Lemma lem17076 (p : Prop) (q : Prop) : ((term3 q p) = ((term5 q) = (term6 q))) = (((term8 p q) = (term9 p q)) = ((term5 q) = (term6 q))).
Proof. exact (MK_COMB (@lem17074 p q) (@lem17075 q)). Qed.
Lemma lem17077 (p : Prop) (q : Prop) : ((term3 q p) = (term4 q)) = (((term8 p q) = (term9 p q)) = ((term5 q) = (term6 q))).
Proof. exact (TRANS (@lem17071 p q) (@lem17076 p q)). Qed.
Lemma lem17078 (q : Prop) (p : Prop) (h1 : p = True) : ((term8 p q) = (term9 p q)) = ((term5 q) = (term6 q)).
Proof. exact (EQ_MP (@lem17077 p q) (@lem17068 q p h1)). Qed.
Lemma lem17079 (q : Prop) (p : Prop) (h1 : p = True) : ((term5 q) = (term6 q)) = ((term8 p q) = (term9 p q)).
Proof. exact (SYM (@lem17078 q p h1)). Qed.
Lemma lem17080 (q : Prop) : (term2 q) = (term2 q).
Proof. exact (eq_refl (term2 q)). Qed.
Lemma lem17081 (q : Prop) (p : Prop) (h1 : p = False) : (term3 q p) = (term11 q).
Proof. exact (MK_COMB (@lem17080 q) (@lem17058 p h1)). Qed.
Lemma lem17082 (q : Prop) : (term11 q) = ((term12 q) = (term13 q)).
Proof. exact (eq_refl (term11 q)). Qed.
Lemma lem17083 (q : Prop) (p : Prop) : (term7 q p) = (term7 q p).
Proof. exact (eq_refl (term7 q p)). Qed.
Lemma lem17084 (p : Prop) (q : Prop) : ((term3 q p) = (term11 q)) = ((term3 q p) = ((term12 q) = (term13 q))).
Proof. exact (MK_COMB (@lem17083 q p) (@lem17082 q)). Qed.
Lemma lem17085 (p : Prop) (q : Prop) : (term3 q p) = ((term8 p q) = (term9 p q)).
Proof. exact (eq_refl (term3 q p)). Qed.
Lemma lem17086 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem17087 (p : Prop) (q : Prop) : (term7 q p) = (term10 p q).
Proof. exact (MK_COMB (@lem17086) (@lem17085 p q)). Qed.
Lemma lem17088 (q : Prop) : ((term12 q) = (term13 q)) = ((term12 q) = (term13 q)).
Proof. exact (eq_refl ((term12 q) = (term13 q))). Qed.
Lemma lem17089 (p : Prop) (q : Prop) : ((term3 q p) = ((term12 q) = (term13 q))) = (((term8 p q) = (term9 p q)) = ((term12 q) = (term13 q))).
Proof. exact (MK_COMB (@lem17087 p q) (@lem17088 q)). Qed.
Lemma lem17090 (p : Prop) (q : Prop) : ((term3 q p) = (term11 q)) = (((term8 p q) = (term9 p q)) = ((term12 q) = (term13 q))).
Proof. exact (TRANS (@lem17084 p q) (@lem17089 p q)). Qed.
Lemma lem17091 (q : Prop) (p : Prop) (h1 : p = False) : ((term8 p q) = (term9 p q)) = ((term12 q) = (term13 q)).
Proof. exact (EQ_MP (@lem17090 p q) (@lem17081 q p h1)). Qed.
Lemma lem17092 (q : Prop) (p : Prop) (h1 : p = False) : ((term12 q) = (term13 q)) = ((term8 p q) = (term9 p q)).
Proof. exact (SYM (@lem17091 q p h1)). Qed.
Lemma lem17096 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem17097 (q : Prop) : (True \/ q) = True.
Proof. exact (@lem17096 q). Qed.
Lemma lem17098 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem17099 (q : Prop) : (term5 q) = (~ True).
Proof. exact (MK_COMB (@lem17098) (@lem17097 q)). Qed.
Lemma lem17101 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem17102 (q : Prop) : (term5 q) = False.
Proof. exact (TRANS (@lem17099 q) (@lem17101)). Qed.
Lemma lem17103 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem17104 (q : Prop) : (term14 q) = (@eq Prop False).
Proof. exact (MK_COMB (@lem17103) (@lem17102 q)). Qed.
Lemma lem17108 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem17109 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem17110 : term15 = (and False).
Proof. exact (MK_COMB (@lem17109) (@lem17108)). Qed.
Lemma lem17111 (q : Prop) : (~ q) = (~ q).
Proof. exact (eq_refl (~ q)). Qed.
Lemma lem17112 (q : Prop) : (term6 q) = (term16 q).
Proof. exact (MK_COMB (@lem17110) (@lem17111 q)). Qed.
Lemma lem17114 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem17115 (q : Prop) : (term16 q) = False.
Proof. exact (@lem17114 (~ q)). Qed.
Lemma lem17116 (q : Prop) : (term6 q) = False.
Proof. exact (TRANS (@lem17112 q) (@lem17115 q)). Qed.
Lemma lem17117 (q : Prop) : ((term5 q) = (term6 q)) = (False = False).
Proof. exact (MK_COMB (@lem17104 q) (@lem17116 q)). Qed.
Lemma lem17119 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem17120 : (False = False) = (~ False).
Proof. exact (@lem17119 False). Qed.
Lemma lem17122 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem17123 : (False = False) = True.
Proof. exact (TRANS (@lem17120) (@lem17122)). Qed.
Lemma lem17124 (q : Prop) : ((term5 q) = (term6 q)) = True.
Proof. exact (TRANS (@lem17117 q) (@lem17123)). Qed.
Lemma lem17125 (q : Prop) : True = ((term5 q) = (term6 q)).
Proof. exact (SYM (@lem17124 q)). Qed.
Lemma lem17126 (q : Prop) : (term5 q) = (term6 q).
Proof. exact (EQ_MP (@lem17125 q) (@lem0)). Qed.
Lemma lem17130 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem17131 (q : Prop) : (False \/ q) = q.
Proof. exact (@lem17130 q). Qed.
Lemma lem17132 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem17133 (q : Prop) : (term12 q) = (~ q).
Proof. exact (MK_COMB (@lem17132) (@lem17131 q)). Qed.
Lemma lem17134 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem17135 (q : Prop) : (term17 q) = (term18 q).
Proof. exact (MK_COMB (@lem17134) (@lem17133 q)). Qed.
Lemma lem17139 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem17140 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem17141 : term19 = (and True).
Proof. exact (MK_COMB (@lem17140) (@lem17139)). Qed.
Lemma lem17142 (q : Prop) : (~ q) = (~ q).
Proof. exact (eq_refl (~ q)). Qed.
Lemma lem17143 (q : Prop) : (term13 q) = (term20 q).
Proof. exact (MK_COMB (@lem17141) (@lem17142 q)). Qed.
Lemma lem17145 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem17146 (q : Prop) : (term20 q) = (~ q).
Proof. exact (@lem17145 (~ q)). Qed.
Lemma lem17147 (q : Prop) : (term13 q) = (~ q).
Proof. exact (TRANS (@lem17143 q) (@lem17146 q)). Qed.
Lemma lem17148 (q : Prop) : ((term12 q) = (term13 q)) = ((~ q) = (~ q)).
Proof. exact (MK_COMB (@lem17135 q) (@lem17147 q)). Qed.
Lemma lem17150 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem17151 (x : Prop) : (x = x) = True.
Proof. exact (@lem17150 Prop x). Qed.
Lemma lem17152 (q : Prop) : ((~ q) = (~ q)) = True.
Proof. exact (@lem17151 (~ q)). Qed.
Lemma lem17153 (q : Prop) : ((term12 q) = (term13 q)) = True.
Proof. exact (TRANS (@lem17148 q) (@lem17152 q)). Qed.
Lemma lem17154 (q : Prop) : True = ((term12 q) = (term13 q)).
Proof. exact (SYM (@lem17153 q)). Qed.
Lemma lem17155 (q : Prop) : (term12 q) = (term13 q).
Proof. exact (EQ_MP (@lem17154 q) (@lem0)). Qed.
Lemma lem17156 (q : Prop) (p : Prop) (h1 : p = False) : (term8 p q) = (term9 p q).
Proof. exact (EQ_MP (@lem17092 q p h1) (@lem17155 q)). Qed.
Lemma lem17157 (q : Prop) (p : Prop) (h1 : p = True) : (term8 p q) = (term9 p q).
Proof. exact (EQ_MP (@lem17079 q p h1) (@lem17126 q)). Qed.
Lemma lem17160 (p : Prop) (q : Prop) : (term8 p q) = (term9 p q).
Proof. exact (or_elim (@lem17056 p) (fun h0 : p = True => @lem17157 q p h0) (fun h0 : p = False => @lem17156 q p h0)). Qed.
