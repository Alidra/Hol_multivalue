Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm19158_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem19047 (a : Prop) : term0 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem19048 (a : Prop) : (term0 a) = (term1 a).
Proof. exact (eq_refl (term0 a)). Qed.
Lemma lem19049 (a : Prop) : term1 a.
Proof. exact (EQ_MP (@lem19048 a) (@lem19047 a)). Qed.
Lemma lem19050 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem19051 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem19066 (b : Prop) (c : Prop) : (term2 b c) = (term2 b c).
Proof. exact (eq_refl (term2 b c)). Qed.
Lemma lem19067 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : (term3 b c a) = (term4 b c).
Proof. exact (MK_COMB (@lem19066 b c) (@lem19050 a h1)). Qed.
Lemma lem19068 (b : Prop) (c : Prop) : (term4 b c) = ((term5 b c) = (term6 b c)).
Proof. exact (eq_refl (term4 b c)). Qed.
Lemma lem19069 (b : Prop) (c : Prop) (a : Prop) : (term7 b c a) = (term7 b c a).
Proof. exact (eq_refl (term7 b c a)). Qed.
Lemma lem19070 (a : Prop) (b : Prop) (c : Prop) : ((term3 b c a) = (term4 b c)) = ((term3 b c a) = ((term5 b c) = (term6 b c))).
Proof. exact (MK_COMB (@lem19069 b c a) (@lem19068 b c)). Qed.
Lemma lem19071 (b : Prop) (a : Prop) (c : Prop) : (term3 b c a) = ((term8 a b c) = (term9 b a c)).
Proof. exact (eq_refl (term3 b c a)). Qed.
Lemma lem19072 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem19073 (b : Prop) (a : Prop) (c : Prop) : (term7 b c a) = (term10 b a c).
Proof. exact (MK_COMB (@lem19072) (@lem19071 b a c)). Qed.
Lemma lem19074 (b : Prop) (c : Prop) : ((term5 b c) = (term6 b c)) = ((term5 b c) = (term6 b c)).
Proof. exact (eq_refl ((term5 b c) = (term6 b c))). Qed.
Lemma lem19075 (a : Prop) (b : Prop) (c : Prop) : ((term3 b c a) = ((term5 b c) = (term6 b c))) = (((term8 a b c) = (term9 b a c)) = ((term5 b c) = (term6 b c))).
Proof. exact (MK_COMB (@lem19073 b a c) (@lem19074 b c)). Qed.
Lemma lem19076 (a : Prop) (b : Prop) (c : Prop) : ((term3 b c a) = (term4 b c)) = (((term8 a b c) = (term9 b a c)) = ((term5 b c) = (term6 b c))).
Proof. exact (TRANS (@lem19070 a b c) (@lem19075 a b c)). Qed.
Lemma lem19077 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : ((term8 a b c) = (term9 b a c)) = ((term5 b c) = (term6 b c)).
Proof. exact (EQ_MP (@lem19076 a b c) (@lem19067 b c a h1)). Qed.
Lemma lem19078 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : ((term5 b c) = (term6 b c)) = ((term8 a b c) = (term9 b a c)).
Proof. exact (SYM (@lem19077 b c a h1)). Qed.
Lemma lem19079 (b : Prop) (c : Prop) : (term2 b c) = (term2 b c).
Proof. exact (eq_refl (term2 b c)). Qed.
Lemma lem19080 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : (term3 b c a) = (term11 b c).
Proof. exact (MK_COMB (@lem19079 b c) (@lem19051 a h1)). Qed.
Lemma lem19081 (b : Prop) (c : Prop) : (term11 b c) = ((term12 b c) = (term13 b c)).
Proof. exact (eq_refl (term11 b c)). Qed.
Lemma lem19082 (b : Prop) (c : Prop) (a : Prop) : (term7 b c a) = (term7 b c a).
Proof. exact (eq_refl (term7 b c a)). Qed.
Lemma lem19083 (a : Prop) (b : Prop) (c : Prop) : ((term3 b c a) = (term11 b c)) = ((term3 b c a) = ((term12 b c) = (term13 b c))).
Proof. exact (MK_COMB (@lem19082 b c a) (@lem19081 b c)). Qed.
Lemma lem19084 (b : Prop) (a : Prop) (c : Prop) : (term3 b c a) = ((term8 a b c) = (term9 b a c)).
Proof. exact (eq_refl (term3 b c a)). Qed.
Lemma lem19085 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem19086 (b : Prop) (a : Prop) (c : Prop) : (term7 b c a) = (term10 b a c).
Proof. exact (MK_COMB (@lem19085) (@lem19084 b a c)). Qed.
Lemma lem19087 (b : Prop) (c : Prop) : ((term12 b c) = (term13 b c)) = ((term12 b c) = (term13 b c)).
Proof. exact (eq_refl ((term12 b c) = (term13 b c))). Qed.
Lemma lem19088 (a : Prop) (b : Prop) (c : Prop) : ((term3 b c a) = ((term12 b c) = (term13 b c))) = (((term8 a b c) = (term9 b a c)) = ((term12 b c) = (term13 b c))).
Proof. exact (MK_COMB (@lem19086 b a c) (@lem19087 b c)). Qed.
Lemma lem19089 (a : Prop) (b : Prop) (c : Prop) : ((term3 b c a) = (term11 b c)) = (((term8 a b c) = (term9 b a c)) = ((term12 b c) = (term13 b c))).
Proof. exact (TRANS (@lem19083 a b c) (@lem19088 a b c)). Qed.
Lemma lem19090 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : ((term8 a b c) = (term9 b a c)) = ((term12 b c) = (term13 b c)).
Proof. exact (EQ_MP (@lem19089 a b c) (@lem19080 b c a h1)). Qed.
Lemma lem19091 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : ((term12 b c) = (term13 b c)) = ((term8 a b c) = (term9 b a c)).
Proof. exact (SYM (@lem19090 b c a h1)). Qed.
Lemma lem19095 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem19096 (b : Prop) (c : Prop) : (term5 b c) = (b \/ c).
Proof. exact (@lem19095 (b \/ c)). Qed.
Lemma lem19099 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem19100 (b : Prop) (c : Prop) : (term14 b c) = (term15 b c).
Proof. exact (MK_COMB (@lem19099) (@lem19096 b c)). Qed.
Lemma lem19104 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem19105 (b : Prop) : (True /\ b) = b.
Proof. exact (@lem19104 b). Qed.
Lemma lem19106 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem19107 (b : Prop) : (term16 b) = (or b).
Proof. exact (MK_COMB (@lem19106) (@lem19105 b)). Qed.
Lemma lem19109 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem19110 (c : Prop) : (True /\ c) = c.
Proof. exact (@lem19109 c). Qed.
Lemma lem19111 (b : Prop) (c : Prop) : (term6 b c) = (b \/ c).
Proof. exact (MK_COMB (@lem19107 b) (@lem19110 c)). Qed.
Lemma lem19114 (b : Prop) (c : Prop) : ((term5 b c) = (term6 b c)) = ((b \/ c) = (b \/ c)).
Proof. exact (MK_COMB (@lem19100 b c) (@lem19111 b c)). Qed.
Lemma lem19116 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem19117 (x : Prop) : (x = x) = True.
Proof. exact (@lem19116 Prop x). Qed.
Lemma lem19118 (b : Prop) (c : Prop) : ((b \/ c) = (b \/ c)) = True.
Proof. exact (@lem19117 (b \/ c)). Qed.
Lemma lem19119 (b : Prop) (c : Prop) : ((term5 b c) = (term6 b c)) = True.
Proof. exact (TRANS (@lem19114 b c) (@lem19118 b c)). Qed.
Lemma lem19120 (b : Prop) (c : Prop) : True = ((term5 b c) = (term6 b c)).
Proof. exact (SYM (@lem19119 b c)). Qed.
Lemma lem19121 (b : Prop) (c : Prop) : (term5 b c) = (term6 b c).
Proof. exact (EQ_MP (@lem19120 b c) (@lem0)). Qed.
Lemma lem19125 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem19126 (b : Prop) (c : Prop) : (term12 b c) = False.
Proof. exact (@lem19125 (b \/ c)). Qed.
Lemma lem19127 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem19128 (b : Prop) (c : Prop) : (term17 b c) = (@eq Prop False).
Proof. exact (MK_COMB (@lem19127) (@lem19126 b c)). Qed.
Lemma lem19132 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem19133 (b : Prop) : (False /\ b) = False.
Proof. exact (@lem19132 b). Qed.
Lemma lem19134 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem19135 (b : Prop) : (term18 b) = (or False).
Proof. exact (MK_COMB (@lem19134) (@lem19133 b)). Qed.
Lemma lem19137 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem19138 (c : Prop) : (False /\ c) = False.
Proof. exact (@lem19137 c). Qed.
Lemma lem19139 (b : Prop) (c : Prop) : (term13 b c) = (False \/ False).
Proof. exact (MK_COMB (@lem19135 b) (@lem19138 c)). Qed.
Lemma lem19141 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem19142 : (False \/ False) = False.
Proof. exact (@lem19141 False). Qed.
Lemma lem19143 (b : Prop) (c : Prop) : (term13 b c) = False.
Proof. exact (TRANS (@lem19139 b c) (@lem19142)). Qed.
Lemma lem19144 (b : Prop) (c : Prop) : ((term12 b c) = (term13 b c)) = (False = False).
Proof. exact (MK_COMB (@lem19128 b c) (@lem19143 b c)). Qed.
Lemma lem19146 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem19147 : (False = False) = (~ False).
Proof. exact (@lem19146 False). Qed.
Lemma lem19149 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem19150 : (False = False) = True.
Proof. exact (TRANS (@lem19147) (@lem19149)). Qed.
Lemma lem19151 (b : Prop) (c : Prop) : ((term12 b c) = (term13 b c)) = True.
Proof. exact (TRANS (@lem19144 b c) (@lem19150)). Qed.
Lemma lem19152 (b : Prop) (c : Prop) : True = ((term12 b c) = (term13 b c)).
Proof. exact (SYM (@lem19151 b c)). Qed.
Lemma lem19153 (b : Prop) (c : Prop) : (term12 b c) = (term13 b c).
Proof. exact (EQ_MP (@lem19152 b c) (@lem0)). Qed.
Lemma lem19154 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : (term8 a b c) = (term9 b a c).
Proof. exact (EQ_MP (@lem19091 b c a h1) (@lem19153 b c)). Qed.
Lemma lem19155 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : (term8 a b c) = (term9 b a c).
Proof. exact (EQ_MP (@lem19078 b c a h1) (@lem19121 b c)). Qed.
Lemma lem19158 (b : Prop) (a : Prop) (c : Prop) : (term8 a b c) = (term9 b a c).
Proof. exact (or_elim (@lem19049 a) (fun h0 : a = True => @lem19155 b c a h0) (fun h0 : a = False => @lem19154 b c a h0)). Qed.
