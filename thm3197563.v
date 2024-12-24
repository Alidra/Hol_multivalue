Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3197563_term_abbrevs.
Require Import thm0_spec.
Require Import thm32_spec.
Require Import thm37_spec.
Require Import thm51_spec.
Require Import thm7_spec.
Require Import thm7058_spec.
Require Import thm7129_spec.
Require Import thm7400_spec.
Require Import thm9103_spec.
Require Import thm9104_spec.
Require Import thm9120_spec.
Lemma lem3197082 {A : Type'} (a : A -> Prop) (h1 : a = (@EMPTY A)) : a = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem3197083 {A : Type'} (FINITE' : type686 A) (h1 : FINITE' (@EMPTY A)) : FINITE' (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem3197084 {A : Type'} (FINITE' : type686 A) : FINITE' = FINITE'.
Proof. exact (eq_refl FINITE'). Qed.
Lemma lem3197085 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (h1 : a = (@EMPTY A)) : (FINITE' a) = (FINITE' (@EMPTY A)).
Proof. exact (MK_COMB (@lem3197084 A FINITE') (@lem3197082 A a h1)). Qed.
Lemma lem3197086 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (h1 : a = (@EMPTY A)) : (FINITE' (@EMPTY A)) = (FINITE' a).
Proof. exact (SYM (@lem3197085 A FINITE' a h1)). Qed.
Lemma lem3197087 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (h1 : FINITE' (@EMPTY A)) (h2 : a = (@EMPTY A)) : FINITE' a.
Proof. exact (EQ_MP (@lem3197086 A FINITE' a h2) (@lem3197083 A FINITE' h1)). Qed.
Lemma lem3197088 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : FINITE' (@EMPTY A)) : term0 A FINITE' a.
Proof. exact (fun h0 : a = (@EMPTY A) => @lem3197087 A FINITE' a h1 h0). Qed.
Lemma lem3197089 {A : Type'} (a : A -> Prop) (h1 : a = (@EMPTY A)) : a = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem3197090 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (h1 : FINITE' (@EMPTY A)) (h2 : a = (@EMPTY A)) : FINITE' a.
Proof. exact (@lem3197088 A a FINITE' h1 (@lem3197089 A a h2)). Qed.
Lemma lem3197091 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : FINITE' (@EMPTY A)) : term0 A FINITE' a.
Proof. exact (fun h0 : a = (@EMPTY A) => @lem3197090 A FINITE' a h1 h0). Qed.
Lemma lem3197092 {A : Type'} (FINITE' : type686 A) (h1 : FINITE' (@EMPTY A)) : term1 A FINITE'.
Proof. exact (fun a : A -> Prop => @lem3197091 A a FINITE' h1). Qed.
Lemma lem3197093 {A : Type'} (FINITE' : type686 A) (h1 : term1 A FINITE') : term1 A FINITE'.
Proof. exact (h1). Qed.
Lemma lem3197094 {A : Type'} (FINITE' : type686 A) (h1 : term1 A FINITE') : term2 A FINITE'.
Proof. exact (@lem3197093 A FINITE' h1 (@EMPTY A)). Qed.
Lemma lem3197095 {A : Type'} (FINITE' : type686 A) : (term2 A FINITE') = (term3 A FINITE').
Proof. exact (eq_refl (term2 A FINITE')). Qed.
Lemma lem3197096 {A : Type'} (FINITE' : type686 A) (h1 : term1 A FINITE') : term3 A FINITE'.
Proof. exact (EQ_MP (@lem3197095 A FINITE') (@lem3197094 A FINITE' h1)). Qed.
Lemma lem3197097 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (eq_refl (@EMPTY A)). Qed.
Lemma lem3197098 {A : Type'} (FINITE' : type686 A) (h1 : term1 A FINITE') : FINITE' (@EMPTY A).
Proof. exact (@lem3197096 A FINITE' h1 (@lem3197097 A)). Qed.
Lemma lem3197099 {A : Type'} (FINITE' : type686 A) : term4 A FINITE'.
Proof. exact (fun h0 : term1 A FINITE' => @lem3197098 A FINITE' h0). Qed.
Lemma lem3197100 {A : Type'} (FINITE' : type686 A) : term5 A FINITE'.
Proof. exact (fun h0 : FINITE' (@EMPTY A) => @lem3197092 A FINITE' h0). Qed.
Lemma lem3197101 {A : Type'} (FINITE' : type686 A) : term6 A FINITE'.
Proof. exact (conj (@lem3197100 A FINITE') (@lem3197099 A FINITE')). Qed.
Lemma lem3197102 {A : Type'} (FINITE' : type686 A) : (term6 A FINITE') = ((FINITE' (@EMPTY A)) = (term1 A FINITE')).
Proof. exact (@lem32 (FINITE' (@EMPTY A)) (term1 A FINITE')). Qed.
Lemma lem3197103 {A : Type'} (FINITE' : type686 A) : (FINITE' (@EMPTY A)) = (term1 A FINITE').
Proof. exact (EQ_MP (@lem3197102 A FINITE') (@lem3197101 A FINITE')). Qed.
Lemma lem3197104 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (h1 : term0 A FINITE' a) : term0 A FINITE' a.
Proof. exact (h1). Qed.
Lemma lem3197105 {A : Type'} (a : A -> Prop) (h1 : a = (@EMPTY A)) : a = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem3197106 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (h1 : a = (@EMPTY A)) (h2 : term0 A FINITE' a) : FINITE' a.
Proof. exact (@lem3197104 A FINITE' a h2 (@lem3197105 A a h1)). Qed.
Lemma lem3197107 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (h1 : a = (@EMPTY A)) : term7 A FINITE' a.
Proof. exact (fun h0 : term0 A FINITE' a => @lem3197106 A FINITE' a h1 h0). Qed.
Lemma lem3197108 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (h1 : term0 A FINITE' a) : term0 A FINITE' a.
Proof. exact (h1). Qed.
Lemma lem3197109 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (h1 : a = (@EMPTY A)) (h2 : term0 A FINITE' a) : FINITE' a.
Proof. exact (@lem3197107 A FINITE' a h1 (@lem3197108 A FINITE' a h2)). Qed.
Lemma lem3197110 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (h1 : term0 A FINITE' a) : term0 A FINITE' a.
Proof. exact (fun h0 : a = (@EMPTY A) => @lem3197109 A FINITE' a h0 h1). Qed.
Lemma lem3197111 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (h1 : term0 A FINITE' a) : term0 A FINITE' a.
Proof. exact (h1). Qed.
Lemma lem3197112 {A : Type'} (a : A -> Prop) (h1 : a = (@EMPTY A)) : a = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem3197113 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (h1 : a = (@EMPTY A)) (h2 : term0 A FINITE' a) : FINITE' a.
Proof. exact (@lem3197111 A FINITE' a h2 (@lem3197112 A a h1)). Qed.
Lemma lem3197114 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (h1 : term0 A FINITE' a) : term0 A FINITE' a.
Proof. exact (fun h0 : a = (@EMPTY A) => @lem3197113 A FINITE' a h0 h1). Qed.
Lemma lem3197115 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) : term8 A FINITE' a.
Proof. exact (fun h0 : term0 A FINITE' a => @lem3197114 A FINITE' a h0). Qed.
Lemma lem3197116 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) : term8 A FINITE' a.
Proof. exact (fun h0 : term0 A FINITE' a => @lem3197110 A FINITE' a h0). Qed.
Lemma lem3197117 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) : term9 A FINITE' a.
Proof. exact (conj (@lem3197116 A FINITE' a) (@lem3197115 A FINITE' a)). Qed.
Lemma lem3197118 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) : (term9 A FINITE' a) = ((term0 A FINITE' a) = (term0 A FINITE' a)).
Proof. exact (@lem32 (term0 A FINITE' a) (term0 A FINITE' a)). Qed.
Lemma lem3197119 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) : (term0 A FINITE' a) = (term0 A FINITE' a).
Proof. exact (EQ_MP (@lem3197118 A FINITE' a) (@lem3197117 A FINITE' a)). Qed.
Lemma lem3197120 {A : Type'} (FINITE' : type686 A) : (term10 A FINITE') = (term10 A FINITE').
Proof. exact (fun_ext (fun a : A -> Prop => @lem3197119 A FINITE' a)). Qed.
Lemma lem3197121 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3197122 {A : Type'} (FINITE' : type686 A) : (term1 A FINITE') = (term1 A FINITE').
Proof. exact (MK_COMB (@lem3197121 A) (@lem3197120 A FINITE')). Qed.
Lemma lem3197123 {A : Type'} (FINITE' : type686 A) : (FINITE' (@EMPTY A)) = (term1 A FINITE').
Proof. exact (TRANS (@lem3197103 A FINITE') (@lem3197122 A FINITE')). Qed.
Lemma lem3197124 {A : Type'} (a : A -> Prop) (x : A) (FINITE' : type686 A) (s : A -> Prop) (h1 : term11 A a x FINITE' s) : term11 A a x FINITE' s.
Proof. exact (h1). Qed.
Lemma lem3197125 {A : Type'} (a : A -> Prop) (x : A) (FINITE' : type686 A) (s : A -> Prop) (h1 : term11 A a x FINITE' s) : FINITE' s.
Proof. exact (proj2 (@lem3197124 A a x FINITE' s h1)). Qed.
Lemma lem3197126 {A : Type'} (a : A -> Prop) (x : A) (FINITE' : type686 A) (s : A -> Prop) (h1 : term11 A a x FINITE' s) : a = (@INSERT A x s).
Proof. exact (proj1 (@lem3197124 A a x FINITE' s h1)). Qed.
Lemma lem3197127 {A : Type'} (FINITE' : type686 A) (h1 : term12 A FINITE') : term12 A FINITE'.
Proof. exact (h1). Qed.
Lemma lem3197128 {A : Type'} (x : A) (FINITE' : type686 A) (h1 : term12 A FINITE') : term13 A FINITE' x.
Proof. exact (@lem3197127 A FINITE' h1 x). Qed.
Lemma lem3197129 {A : Type'} (FINITE' : type686 A) (x : A) : (term13 A FINITE' x) = (term14 A FINITE' x).
Proof. exact (eq_refl (term13 A FINITE' x)). Qed.
Lemma lem3197130 {A : Type'} (x : A) (FINITE' : type686 A) (h1 : term12 A FINITE') : term14 A FINITE' x.
Proof. exact (EQ_MP (@lem3197129 A FINITE' x) (@lem3197128 A x FINITE' h1)). Qed.
Lemma lem3197131 {A : Type'} (x : A) (s : A -> Prop) (FINITE' : type686 A) (h1 : term12 A FINITE') : term15 A FINITE' x s.
Proof. exact (@lem3197130 A x FINITE' h1 s). Qed.
Lemma lem3197132 {A : Type'} (FINITE' : type686 A) (x : A) (s : A -> Prop) : (term15 A FINITE' x s) = (term16 A FINITE' x s).
Proof. exact (eq_refl (term15 A FINITE' x s)). Qed.
Lemma lem3197133 {A : Type'} (x : A) (s : A -> Prop) (FINITE' : type686 A) (h1 : term12 A FINITE') : term16 A FINITE' x s.
Proof. exact (EQ_MP (@lem3197132 A FINITE' x s) (@lem3197131 A x s FINITE' h1)). Qed.
Lemma lem3197134 {A : Type'} (a : A -> Prop) (x : A) (FINITE' : type686 A) (s : A -> Prop) (h1 : term12 A FINITE') (h2 : term11 A a x FINITE' s) : term17 A FINITE' x s.
Proof. exact (@lem3197133 A x s FINITE' h1 (@lem3197125 A a x FINITE' s h2)). Qed.
Lemma lem3197135 {A : Type'} (FINITE' : type686 A) : FINITE' = FINITE'.
Proof. exact (eq_refl FINITE'). Qed.
Lemma lem3197136 {A : Type'} (a : A -> Prop) (x : A) (FINITE' : type686 A) (s : A -> Prop) (h1 : term11 A a x FINITE' s) : (FINITE' a) = (term17 A FINITE' x s).
Proof. exact (MK_COMB (@lem3197135 A FINITE') (@lem3197126 A a x FINITE' s h1)). Qed.
Lemma lem3197137 {A : Type'} (a : A -> Prop) (x : A) (FINITE' : type686 A) (s : A -> Prop) (h1 : term11 A a x FINITE' s) : (term17 A FINITE' x s) = (FINITE' a).
Proof. exact (SYM (@lem3197136 A a x FINITE' s h1)). Qed.
Lemma lem3197138 {A : Type'} (a : A -> Prop) (x : A) (FINITE' : type686 A) (s : A -> Prop) (h1 : term12 A FINITE') (h2 : term11 A a x FINITE' s) : FINITE' a.
Proof. exact (EQ_MP (@lem3197137 A a x FINITE' s h2) (@lem3197134 A a x FINITE' s h1 h2)). Qed.
Lemma lem3197139 {A : Type'} (x : A) (s : A -> Prop) (a : A -> Prop) (FINITE' : type686 A) (h1 : term12 A FINITE') : term18 A x s FINITE' a.
Proof. exact (fun h0 : term11 A a x FINITE' s => @lem3197138 A a x FINITE' s h1 h0). Qed.
Lemma lem3197140 {A : Type'} (a : A -> Prop) (x : A) (FINITE' : type686 A) (s : A -> Prop) (h1 : term11 A a x FINITE' s) : term11 A a x FINITE' s.
Proof. exact (h1). Qed.
Lemma lem3197141 {A : Type'} (a : A -> Prop) (x : A) (FINITE' : type686 A) (s : A -> Prop) (h1 : term12 A FINITE') (h2 : term11 A a x FINITE' s) : FINITE' a.
Proof. exact (@lem3197139 A x s a FINITE' h1 (@lem3197140 A a x FINITE' s h2)). Qed.
Lemma lem3197142 {A : Type'} (x : A) (s : A -> Prop) (a : A -> Prop) (FINITE' : type686 A) (h1 : term12 A FINITE') : term18 A x s FINITE' a.
Proof. exact (fun h0 : term11 A a x FINITE' s => @lem3197141 A a x FINITE' s h1 h0). Qed.
Lemma lem3197143 {A : Type'} (x : A) (a : A -> Prop) (FINITE' : type686 A) (h1 : term12 A FINITE') : term19 A x FINITE' a.
Proof. exact (fun s : A -> Prop => @lem3197142 A x s a FINITE' h1). Qed.
Lemma lem3197144 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term12 A FINITE') : term20 A FINITE' a.
Proof. exact (fun x : A => @lem3197143 A x a FINITE' h1). Qed.
Lemma lem3197145 {A : Type'} (FINITE' : type686 A) (h1 : term12 A FINITE') : term21 A FINITE'.
Proof. exact (fun a : A -> Prop => @lem3197144 A a FINITE' h1). Qed.
Lemma lem3197146 {A : Type'} (FINITE' : type686 A) (h1 : term21 A FINITE') : term21 A FINITE'.
Proof. exact (h1). Qed.
Lemma lem3197147 {A : Type'} (x : A) (s : A -> Prop) (FINITE' : type686 A) (h1 : term21 A FINITE') : term22 A FINITE' x s.
Proof. exact (@lem3197146 A FINITE' h1 (@INSERT A x s)). Qed.
Lemma lem3197148 {A : Type'} (FINITE' : type686 A) (x : A) (s : A -> Prop) : (term22 A FINITE' x s) = (term23 A FINITE' x s).
Proof. exact (eq_refl (term22 A FINITE' x s)). Qed.
Lemma lem3197149 {A : Type'} (x : A) (s : A -> Prop) (FINITE' : type686 A) (h1 : term21 A FINITE') : term23 A FINITE' x s.
Proof. exact (EQ_MP (@lem3197148 A FINITE' x s) (@lem3197147 A x s FINITE' h1)). Qed.
Lemma lem3197150 {A : Type'} (s : A -> Prop) (x : A) (FINITE' : type686 A) (h1 : term21 A FINITE') : term24 A FINITE' s x.
Proof. exact (@lem3197149 A x s FINITE' h1 x). Qed.
Lemma lem3197151 {A : Type'} (FINITE' : type686 A) (x : A) (s : A -> Prop) : (term24 A FINITE' s x) = (term25 A FINITE' x s).
Proof. exact (eq_refl (term24 A FINITE' s x)). Qed.
Lemma lem3197152 {A : Type'} (x : A) (s : A -> Prop) (FINITE' : type686 A) (h1 : term21 A FINITE') : term25 A FINITE' x s.
Proof. exact (EQ_MP (@lem3197151 A FINITE' x s) (@lem3197150 A s x FINITE' h1)). Qed.
Lemma lem3197153 {A : Type'} (x : A) (s : A -> Prop) (FINITE' : type686 A) (h1 : term21 A FINITE') : term26 A FINITE' x s.
Proof. exact (@lem3197152 A x s FINITE' h1 s). Qed.
Lemma lem3197154 {A : Type'} (FINITE' : type686 A) (x : A) (s : A -> Prop) : (term26 A FINITE' x s) = (term27 A FINITE' x s).
Proof. exact (eq_refl (term26 A FINITE' x s)). Qed.
Lemma lem3197155 {A : Type'} (x : A) (s : A -> Prop) (FINITE' : type686 A) (h1 : term21 A FINITE') : term27 A FINITE' x s.
Proof. exact (EQ_MP (@lem3197154 A FINITE' x s) (@lem3197153 A x s FINITE' h1)). Qed.
Lemma lem3197156 {A : Type'} (FINITE' : type686 A) (s : A -> Prop) (h1 : FINITE' s) : FINITE' s.
Proof. exact (h1). Qed.
Lemma lem3197157 {A : Type'} (x : A) (s : A -> Prop) : (@INSERT A x s) = (@INSERT A x s).
Proof. exact (eq_refl (@INSERT A x s)). Qed.
Lemma lem3197158 {A : Type'} (x : A) (FINITE' : type686 A) (s : A -> Prop) (h1 : FINITE' s) : term28 A x FINITE' s.
Proof. exact (conj (@lem3197157 A x s) (@lem3197156 A FINITE' s h1)). Qed.
Lemma lem3197159 {A : Type'} (x : A) (FINITE' : type686 A) (s : A -> Prop) (h1 : term21 A FINITE') (h2 : FINITE' s) : term17 A FINITE' x s.
Proof. exact (@lem3197155 A x s FINITE' h1 (@lem3197158 A x FINITE' s h2)). Qed.
Lemma lem3197160 {A : Type'} (x : A) (s : A -> Prop) (FINITE' : type686 A) (h1 : term21 A FINITE') : term16 A FINITE' x s.
Proof. exact (fun h0 : FINITE' s => @lem3197159 A x FINITE' s h1 h0). Qed.
Lemma lem3197161 {A : Type'} (x : A) (FINITE' : type686 A) (h1 : term21 A FINITE') : term14 A FINITE' x.
Proof. exact (fun s : A -> Prop => @lem3197160 A x s FINITE' h1). Qed.
Lemma lem3197162 {A : Type'} (FINITE' : type686 A) (h1 : term21 A FINITE') : term12 A FINITE'.
Proof. exact (fun x : A => @lem3197161 A x FINITE' h1). Qed.
Lemma lem3197163 {A : Type'} (FINITE' : type686 A) : term29 A FINITE'.
Proof. exact (fun h0 : term21 A FINITE' => @lem3197162 A FINITE' h0). Qed.
Lemma lem3197164 {A : Type'} (FINITE' : type686 A) : term30 A FINITE'.
Proof. exact (fun h0 : term12 A FINITE' => @lem3197145 A FINITE' h0). Qed.
Lemma lem3197165 {A : Type'} (FINITE' : type686 A) : term31 A FINITE'.
Proof. exact (conj (@lem3197164 A FINITE') (@lem3197163 A FINITE')). Qed.
Lemma lem3197166 {A : Type'} (FINITE' : type686 A) : (term31 A FINITE') = ((term12 A FINITE') = (term21 A FINITE')).
Proof. exact (@lem32 (term12 A FINITE') (term21 A FINITE')). Qed.
Lemma lem3197167 {A : Type'} (FINITE' : type686 A) : (term12 A FINITE') = (term21 A FINITE').
Proof. exact (EQ_MP (@lem3197166 A FINITE') (@lem3197165 A FINITE')). Qed.
Lemma lem3197168 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (h1 : term20 A FINITE' a) : term20 A FINITE' a.
Proof. exact (h1). Qed.
Lemma lem3197169 {A : Type'} (x : A) (FINITE' : type686 A) (a : A -> Prop) (h1 : term20 A FINITE' a) : term32 A FINITE' a x.
Proof. exact (@lem3197168 A FINITE' a h1 x). Qed.
Lemma lem3197170 {A : Type'} (x : A) (FINITE' : type686 A) (a : A -> Prop) : (term32 A FINITE' a x) = (term19 A x FINITE' a).
Proof. exact (eq_refl (term32 A FINITE' a x)). Qed.
Lemma lem3197171 {A : Type'} (x : A) (FINITE' : type686 A) (a : A -> Prop) (h1 : term20 A FINITE' a) : term19 A x FINITE' a.
Proof. exact (EQ_MP (@lem3197170 A x FINITE' a) (@lem3197169 A x FINITE' a h1)). Qed.
Lemma lem3197172 {A : Type'} (x : A) (s : A -> Prop) (FINITE' : type686 A) (a : A -> Prop) (h1 : term20 A FINITE' a) : term33 A x FINITE' a s.
Proof. exact (@lem3197171 A x FINITE' a h1 s). Qed.
Lemma lem3197173 {A : Type'} (x : A) (s : A -> Prop) (FINITE' : type686 A) (a : A -> Prop) : (term33 A x FINITE' a s) = (term18 A x s FINITE' a).
Proof. exact (eq_refl (term33 A x FINITE' a s)). Qed.
Lemma lem3197174 {A : Type'} (x : A) (s : A -> Prop) (FINITE' : type686 A) (a : A -> Prop) (h1 : term20 A FINITE' a) : term18 A x s FINITE' a.
Proof. exact (EQ_MP (@lem3197173 A x s FINITE' a) (@lem3197172 A x s FINITE' a h1)). Qed.
Lemma lem3197175 {A : Type'} (a : A -> Prop) (x : A) (FINITE' : type686 A) (s : A -> Prop) (h1 : term11 A a x FINITE' s) : term11 A a x FINITE' s.
Proof. exact (h1). Qed.
Lemma lem3197176 {A : Type'} (a : A -> Prop) (x : A) (FINITE' : type686 A) (s : A -> Prop) (h1 : term20 A FINITE' a) (h2 : term11 A a x FINITE' s) : FINITE' a.
Proof. exact (@lem3197174 A x s FINITE' a h1 (@lem3197175 A a x FINITE' s h2)). Qed.
Lemma lem3197177 {A : Type'} (a : A -> Prop) (x : A) (FINITE' : type686 A) (s : A -> Prop) (h1 : term11 A a x FINITE' s) : term34 A FINITE' a.
Proof. exact (fun h0 : term20 A FINITE' a => @lem3197176 A a x FINITE' s h0 h1). Qed.
Lemma lem3197178 {A : Type'} (a : A -> Prop) (x : A) (FINITE' : type686 A) (h1 : term35 A a x FINITE') : term35 A a x FINITE'.
Proof. exact (h1). Qed.
Lemma lem3197179 {A : Type'} (a : A -> Prop) (x : A) (FINITE' : type686 A) (h1 : term35 A a x FINITE') : term34 A FINITE' a.
Proof. exact (ex_elim (@lem3197178 A a x FINITE' h1) (fun s : A -> Prop => fun h0 : term36 A a x FINITE' s => @lem3197177 A a x FINITE' s h0)). Qed.
Lemma lem3197180 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term37 A a FINITE') : term37 A a FINITE'.
Proof. exact (h1). Qed.
Lemma lem3197181 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term37 A a FINITE') : term34 A FINITE' a.
Proof. exact (ex_elim (@lem3197180 A a FINITE' h1) (fun x : A => fun h0 : term38 A a FINITE' x => @lem3197179 A a x FINITE' h0)). Qed.
Lemma lem3197182 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (h1 : term20 A FINITE' a) : term20 A FINITE' a.
Proof. exact (h1). Qed.
Lemma lem3197183 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term20 A FINITE' a) (h2 : term37 A a FINITE') : FINITE' a.
Proof. exact (@lem3197181 A a FINITE' h2 (@lem3197182 A FINITE' a h1)). Qed.
Lemma lem3197184 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (h1 : term20 A FINITE' a) : term39 A FINITE' a.
Proof. exact (fun h0 : term37 A a FINITE' => @lem3197183 A a FINITE' h1 h0). Qed.
Lemma lem3197185 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (h1 : term39 A FINITE' a) : term39 A FINITE' a.
Proof. exact (h1). Qed.
Lemma lem3197186 {A : Type'} (a : A -> Prop) (x : A) (FINITE' : type686 A) (s : A -> Prop) (h1 : term11 A a x FINITE' s) : term11 A a x FINITE' s.
Proof. exact (h1). Qed.
Lemma lem3197187 {A : Type'} (a : A -> Prop) (x : A) (FINITE' : type686 A) (s : A -> Prop) (h1 : term11 A a x FINITE' s) : term35 A a x FINITE'.
Proof. exact (ex_intro (term36 A a x FINITE') s (@lem3197186 A a x FINITE' s h1)). Qed.
Lemma lem3197188 {A : Type'} (a : A -> Prop) (x : A) (FINITE' : type686 A) (s : A -> Prop) (h1 : term11 A a x FINITE' s) : term37 A a FINITE'.
Proof. exact (ex_intro (term38 A a FINITE') x (@lem3197187 A a x FINITE' s h1)). Qed.
Lemma lem3197189 {A : Type'} (x : A) (s : A -> Prop) (FINITE' : type686 A) (a : A -> Prop) (h1 : term11 A a x FINITE' s) (h2 : term39 A FINITE' a) : FINITE' a.
Proof. exact (@lem3197185 A FINITE' a h2 (@lem3197188 A a x FINITE' s h1)). Qed.
Lemma lem3197190 {A : Type'} (x : A) (s : A -> Prop) (FINITE' : type686 A) (a : A -> Prop) (h1 : term39 A FINITE' a) : term18 A x s FINITE' a.
Proof. exact (fun h0 : term11 A a x FINITE' s => @lem3197189 A x s FINITE' a h0 h1). Qed.
Lemma lem3197191 {A : Type'} (x : A) (FINITE' : type686 A) (a : A -> Prop) (h1 : term39 A FINITE' a) : term19 A x FINITE' a.
Proof. exact (fun s : A -> Prop => @lem3197190 A x s FINITE' a h1). Qed.
Lemma lem3197192 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (h1 : term39 A FINITE' a) : term20 A FINITE' a.
Proof. exact (fun x : A => @lem3197191 A x FINITE' a h1). Qed.
Lemma lem3197193 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) : term40 A FINITE' a.
Proof. exact (fun h0 : term39 A FINITE' a => @lem3197192 A FINITE' a h0). Qed.
Lemma lem3197194 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) : term41 A FINITE' a.
Proof. exact (fun h0 : term20 A FINITE' a => @lem3197184 A FINITE' a h0). Qed.
Lemma lem3197195 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) : term42 A FINITE' a.
Proof. exact (conj (@lem3197194 A FINITE' a) (@lem3197193 A FINITE' a)). Qed.
Lemma lem3197196 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) : (term42 A FINITE' a) = ((term20 A FINITE' a) = (term39 A FINITE' a)).
Proof. exact (@lem32 (term20 A FINITE' a) (term39 A FINITE' a)). Qed.
Lemma lem3197197 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) : (term20 A FINITE' a) = (term39 A FINITE' a).
Proof. exact (EQ_MP (@lem3197196 A FINITE' a) (@lem3197195 A FINITE' a)). Qed.
Lemma lem3197198 {A : Type'} (FINITE' : type686 A) : (term43 A FINITE') = (term44 A FINITE').
Proof. exact (fun_ext (fun a : A -> Prop => @lem3197197 A FINITE' a)). Qed.
Lemma lem3197199 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3197200 {A : Type'} (FINITE' : type686 A) : (term21 A FINITE') = (term45 A FINITE').
Proof. exact (MK_COMB (@lem3197199 A) (@lem3197198 A FINITE')). Qed.
Lemma lem3197201 {A : Type'} (FINITE' : type686 A) : (term12 A FINITE') = (term45 A FINITE').
Proof. exact (TRANS (@lem3197167 A FINITE') (@lem3197200 A FINITE')). Qed.
Lemma lem3197203 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem9104 A x) (@lem9103 A x)). Qed.
Lemma lem3197204 (x : Prop) : (x = x) = True.
Proof. exact (@lem3197203 Prop x). Qed.
Lemma lem3197205 {A : Type'} (FINITE' : type686 A) : ((term46 A FINITE') = (term46 A FINITE')) = True.
Proof. exact (@lem3197204 (term46 A FINITE')). Qed.
Lemma lem3197206 {A : Type'} (FINITE' : type686 A) : True = ((term46 A FINITE') = (term46 A FINITE')).
Proof. exact (SYM (@lem3197205 A FINITE')). Qed.
Lemma lem3197207 {A : Type'} (FINITE' : type686 A) : (term46 A FINITE') = (term46 A FINITE').
Proof. exact (EQ_MP (@lem3197206 A FINITE') (@lem0)). Qed.
Lemma lem3197208 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3197209 {A : Type'} (FINITE' : type686 A) : (term47 A FINITE') = (term48 A FINITE').
Proof. exact (MK_COMB (@lem3197208) (@lem3197123 A FINITE')). Qed.
Lemma lem3197210 {A : Type'} (FINITE' : type686 A) : (term49 A FINITE') = (term46 A FINITE').
Proof. exact (MK_COMB (@lem3197209 A FINITE') (@lem3197201 A FINITE')). Qed.
Lemma lem3197211 {A : Type'} (FINITE' : type686 A) : (term49 A FINITE') = (term46 A FINITE').
Proof. exact (TRANS (@lem3197210 A FINITE') (@lem3197207 A FINITE')). Qed.
Lemma lem3197212 {A : Type'} (FINITE' : type686 A) (h1 : term46 A FINITE') : term46 A FINITE'.
Proof. exact (h1). Qed.
Lemma lem3197213 {A : Type'} (FINITE' : type686 A) (h1 : term46 A FINITE') : term45 A FINITE'.
Proof. exact (proj2 (@lem3197212 A FINITE' h1)). Qed.
Lemma lem3197214 {A : Type'} (FINITE' : type686 A) (h1 : term46 A FINITE') : term1 A FINITE'.
Proof. exact (proj1 (@lem3197212 A FINITE' h1)). Qed.
Lemma lem3197215 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term46 A FINITE') : term50 A FINITE' a.
Proof. exact (@lem3197214 A FINITE' h1 a). Qed.
Lemma lem3197216 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) : (term50 A FINITE' a) = (term0 A FINITE' a).
Proof. exact (eq_refl (term50 A FINITE' a)). Qed.
Lemma lem3197217 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term46 A FINITE') : term0 A FINITE' a.
Proof. exact (EQ_MP (@lem3197216 A FINITE' a) (@lem3197215 A a FINITE' h1)). Qed.
Lemma lem3197218 {A : Type'} (a : A -> Prop) (h1 : a = (@EMPTY A)) : a = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem3197219 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (h1 : term46 A FINITE') (h2 : a = (@EMPTY A)) : FINITE' a.
Proof. exact (@lem3197217 A a FINITE' h1 (@lem3197218 A a h2)). Qed.
Lemma lem3197220 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (h1 : a = (@EMPTY A)) : term51 A FINITE' a.
Proof. exact (fun h0 : term46 A FINITE' => @lem3197219 A FINITE' a h0 h1). Qed.
Lemma lem3197221 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term46 A FINITE') : term52 A FINITE' a.
Proof. exact (@lem3197213 A FINITE' h1 a). Qed.
Lemma lem3197222 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) : (term52 A FINITE' a) = (term39 A FINITE' a).
Proof. exact (eq_refl (term52 A FINITE' a)). Qed.
Lemma lem3197223 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term46 A FINITE') : term39 A FINITE' a.
Proof. exact (EQ_MP (@lem3197222 A FINITE' a) (@lem3197221 A a FINITE' h1)). Qed.
Lemma lem3197224 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term37 A a FINITE') : term37 A a FINITE'.
Proof. exact (h1). Qed.
Lemma lem3197225 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term37 A a FINITE') (h2 : term46 A FINITE') : FINITE' a.
Proof. exact (@lem3197223 A a FINITE' h2 (@lem3197224 A a FINITE' h1)). Qed.
Lemma lem3197226 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term37 A a FINITE') : term51 A FINITE' a.
Proof. exact (fun h0 : term46 A FINITE' => @lem3197225 A a FINITE' h1 h0). Qed.
Lemma lem3197227 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term53 A a FINITE') : term53 A a FINITE'.
Proof. exact (h1). Qed.
Lemma lem3197228 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term53 A a FINITE') : term51 A FINITE' a.
Proof. exact (or_elim (@lem3197227 A a FINITE' h1) (fun h0 : a = (@EMPTY A) => @lem3197220 A FINITE' a h0) (fun h0 : term37 A a FINITE' => @lem3197226 A a FINITE' h0)). Qed.
Lemma lem3197229 {A : Type'} (FINITE' : type686 A) (h1 : term46 A FINITE') : term46 A FINITE'.
Proof. exact (h1). Qed.
Lemma lem3197230 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term46 A FINITE') (h2 : term53 A a FINITE') : FINITE' a.
Proof. exact (@lem3197228 A a FINITE' h2 (@lem3197229 A FINITE' h1)). Qed.
Lemma lem3197231 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term46 A FINITE') : term54 A FINITE' a.
Proof. exact (fun h0 : term53 A a FINITE' => @lem3197230 A a FINITE' h1 h0). Qed.
Lemma lem3197232 {A : Type'} (FINITE' : type686 A) (h1 : term46 A FINITE') : term55 A FINITE'.
Proof. exact (fun a : A -> Prop => @lem3197231 A a FINITE' h1). Qed.
Lemma lem3197233 {A : Type'} (FINITE' : type686 A) (h1 : term55 A FINITE') : term55 A FINITE'.
Proof. exact (h1). Qed.
Lemma lem3197234 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term55 A FINITE') : term56 A FINITE' a.
Proof. exact (@lem3197233 A FINITE' h1 a). Qed.
Lemma lem3197235 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) : (term56 A FINITE' a) = (term54 A FINITE' a).
Proof. exact (eq_refl (term56 A FINITE' a)). Qed.
Lemma lem3197236 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term55 A FINITE') : term54 A FINITE' a.
Proof. exact (EQ_MP (@lem3197235 A FINITE' a) (@lem3197234 A a FINITE' h1)). Qed.
Lemma lem3197237 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term53 A a FINITE') : term53 A a FINITE'.
Proof. exact (h1). Qed.
Lemma lem3197238 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term55 A FINITE') (h2 : term53 A a FINITE') : FINITE' a.
Proof. exact (@lem3197236 A a FINITE' h1 (@lem3197237 A a FINITE' h2)). Qed.
Lemma lem3197239 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term53 A a FINITE') : term57 A FINITE' a.
Proof. exact (fun h0 : term55 A FINITE' => @lem3197238 A a FINITE' h0 h1). Qed.
Lemma lem3197240 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term37 A a FINITE') : term37 A a FINITE'.
Proof. exact (h1). Qed.
Lemma lem3197241 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term37 A a FINITE') : term53 A a FINITE'.
Proof. exact (or_intro2 (a = (@EMPTY A)) (@lem3197240 A a FINITE' h1)). Qed.
Lemma lem3197242 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term37 A a FINITE') : (term53 A a FINITE') = (term57 A FINITE' a).
Proof. exact (prop_ext (fun h2 : term53 A a FINITE' => @lem3197239 A a FINITE' h2) (fun h2 : term57 A FINITE' a => @lem3197241 A a FINITE' h1)). Qed.
Lemma lem3197243 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term37 A a FINITE') : term57 A FINITE' a.
Proof. exact (EQ_MP (@lem3197242 A a FINITE' h1) (@lem3197241 A a FINITE' h1)). Qed.
Lemma lem3197244 {A : Type'} (a : A -> Prop) (h1 : a = (@EMPTY A)) : a = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem3197245 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (h1 : a = (@EMPTY A)) : term53 A a FINITE'.
Proof. exact (or_intro1 (@lem3197244 A a h1) (term37 A a FINITE')). Qed.
Lemma lem3197246 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (h1 : a = (@EMPTY A)) : (term53 A a FINITE') = (term57 A FINITE' a).
Proof. exact (prop_ext (fun h2 : term53 A a FINITE' => @lem3197239 A a FINITE' h2) (fun h2 : term57 A FINITE' a => @lem3197245 A FINITE' a h1)). Qed.
Lemma lem3197247 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (h1 : a = (@EMPTY A)) : term57 A FINITE' a.
Proof. exact (EQ_MP (@lem3197246 A FINITE' a h1) (@lem3197245 A FINITE' a h1)). Qed.
Lemma lem3197248 {A : Type'} (FINITE' : type686 A) (h1 : term55 A FINITE') : term55 A FINITE'.
Proof. exact (h1). Qed.
Lemma lem3197249 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term55 A FINITE') (h2 : term37 A a FINITE') : FINITE' a.
Proof. exact (@lem3197243 A a FINITE' h2 (@lem3197248 A FINITE' h1)). Qed.
Lemma lem3197250 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term55 A FINITE') : term39 A FINITE' a.
Proof. exact (fun h0 : term37 A a FINITE' => @lem3197249 A a FINITE' h1 h0). Qed.
Lemma lem3197251 {A : Type'} (FINITE' : type686 A) (h1 : term55 A FINITE') : term45 A FINITE'.
Proof. exact (fun a : A -> Prop => @lem3197250 A a FINITE' h1). Qed.
Lemma lem3197252 {A : Type'} (FINITE' : type686 A) (h1 : term55 A FINITE') : term55 A FINITE'.
Proof. exact (h1). Qed.
Lemma lem3197253 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (h1 : term55 A FINITE') (h2 : a = (@EMPTY A)) : FINITE' a.
Proof. exact (@lem3197247 A FINITE' a h2 (@lem3197252 A FINITE' h1)). Qed.
Lemma lem3197254 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term55 A FINITE') : term0 A FINITE' a.
Proof. exact (fun h0 : a = (@EMPTY A) => @lem3197253 A FINITE' a h1 h0). Qed.
Lemma lem3197255 {A : Type'} (FINITE' : type686 A) (h1 : term55 A FINITE') : term1 A FINITE'.
Proof. exact (fun a : A -> Prop => @lem3197254 A a FINITE' h1). Qed.
Lemma lem3197256 {A : Type'} (FINITE' : type686 A) (h1 : term55 A FINITE') : term46 A FINITE'.
Proof. exact (conj (@lem3197255 A FINITE' h1) (@lem3197251 A FINITE' h1)). Qed.
Lemma lem3197257 {A : Type'} (FINITE' : type686 A) : term58 A FINITE'.
Proof. exact (fun h0 : term55 A FINITE' => @lem3197256 A FINITE' h0). Qed.
Lemma lem3197258 {A : Type'} (FINITE' : type686 A) : term59 A FINITE'.
Proof. exact (fun h0 : term46 A FINITE' => @lem3197232 A FINITE' h0). Qed.
Lemma lem3197259 {A : Type'} (FINITE' : type686 A) : term60 A FINITE'.
Proof. exact (conj (@lem3197258 A FINITE') (@lem3197257 A FINITE')). Qed.
Lemma lem3197260 {A : Type'} (FINITE' : type686 A) : (term60 A FINITE') = ((term46 A FINITE') = (term55 A FINITE')).
Proof. exact (@lem32 (term46 A FINITE') (term55 A FINITE')). Qed.
Lemma lem3197261 {A : Type'} (FINITE' : type686 A) : (term46 A FINITE') = (term55 A FINITE').
Proof. exact (EQ_MP (@lem3197260 A FINITE') (@lem3197259 A FINITE')). Qed.
Lemma lem3197262 {A : Type'} (FINITE' : type686 A) : (term49 A FINITE') = (term55 A FINITE').
Proof. exact (TRANS (@lem3197211 A FINITE') (@lem3197261 A FINITE')). Qed.
Lemma lem3197263 {A : Type'} (FINITE' : type686 A) : (term55 A FINITE') = (term49 A FINITE').
Proof. exact (SYM (@lem3197262 A FINITE')). Qed.
Lemma lem3197264 {A : Type'} (FINITE' : type686 A) (h1 : FINITE' = (term61 A)) : FINITE' = (term61 A).
Proof. exact (h1). Qed.
Lemma lem3197265 {A : Type'} (a : A -> Prop) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3197266 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : FINITE' = (term61 A)) : (FINITE' a) = (term62 A a).
Proof. exact (MK_COMB (@lem3197264 A FINITE' h1) (@lem3197265 A a)). Qed.
Lemma lem3197267 {A : Type'} (a : A -> Prop) : (term62 A a) = (term63 A a).
Proof. exact (eq_refl (term62 A a)). Qed.
Lemma lem3197268 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) : (term64 A FINITE' a) = (term64 A FINITE' a).
Proof. exact (eq_refl (term64 A FINITE' a)). Qed.
Lemma lem3197269 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) : ((FINITE' a) = (term62 A a)) = ((FINITE' a) = (term63 A a)).
Proof. exact (MK_COMB (@lem3197268 A FINITE' a) (@lem3197267 A a)). Qed.
Lemma lem3197270 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : FINITE' = (term61 A)) : (FINITE' a) = (term63 A a).
Proof. exact (EQ_MP (@lem3197269 A FINITE' a) (@lem3197266 A a FINITE' h1)). Qed.
Lemma lem3197271 {A : Type'} (FINITE' : type686 A) (h1 : FINITE' = (term61 A)) : term65 A FINITE'.
Proof. exact (fun a : A -> Prop => @lem3197270 A a FINITE' h1). Qed.
Lemma lem3197272 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : FINITE' = (term61 A)) : term66 A FINITE' a.
Proof. exact (@lem3197271 A FINITE' h1 a). Qed.
Lemma lem3197273 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) : (term66 A FINITE' a) = ((FINITE' a) = (term63 A a)).
Proof. exact (eq_refl (term66 A FINITE' a)). Qed.
Lemma lem3197274 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : FINITE' = (term61 A)) : (FINITE' a) = (term63 A a).
Proof. exact (EQ_MP (@lem3197273 A FINITE' a) (@lem3197272 A a FINITE' h1)). Qed.
Lemma lem3197277 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) : term67 A FINITE' a.
Proof. exact (@lem37 (FINITE' a) (term63 A a)). Qed.
Lemma lem3197278 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : FINITE' = (term61 A)) : term68 A FINITE' a.
Proof. exact (@lem3197277 A FINITE' a (@lem3197274 A a FINITE' h1)). Qed.
Lemma lem3197279 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (h1 : FINITE' a) : FINITE' a.
Proof. exact (h1). Qed.
Lemma lem3197280 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : FINITE' a) (h2 : FINITE' = (term61 A)) : term63 A a.
Proof. exact (@lem3197278 A a FINITE' h2 (@lem3197279 A FINITE' a h1)). Qed.
Lemma lem3197281 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (FINITE'' : type686 A) (h1 : FINITE'' a) (h2 : FINITE'' = (term61 A)) : term69 A a FINITE'.
Proof. exact (@lem3197280 A a FINITE'' h1 h2 FINITE'). Qed.
Lemma lem3197282 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) : (term69 A a FINITE') = (term57 A FINITE' a).
Proof. exact (eq_refl (term69 A a FINITE')). Qed.
Lemma lem3197283 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (FINITE'' : type686 A) (h1 : FINITE'' a) (h2 : FINITE'' = (term61 A)) : term57 A FINITE' a.
Proof. exact (EQ_MP (@lem3197282 A FINITE' a) (@lem3197281 A FINITE' a FINITE'' h1 h2)). Qed.
Lemma lem3197284 {A : Type'} (FINITE' : type686 A) (h1 : term55 A FINITE') : term55 A FINITE'.
Proof. exact (h1). Qed.
Lemma lem3197285 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (FINITE'' : type686 A) (h1 : term55 A FINITE') (h2 : FINITE'' a) (h3 : FINITE'' = (term61 A)) : FINITE' a.
Proof. exact (@lem3197283 A FINITE' a FINITE'' h2 h3 (@lem3197284 A FINITE' h1)). Qed.
Lemma lem3197286 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (FINITE'' : type686 A) (h1 : term55 A FINITE') (h2 : FINITE'' = (term61 A)) : term70 A FINITE'' FINITE' a.
Proof. exact (fun h0 : FINITE'' a => @lem3197285 A FINITE' a FINITE'' h1 h0 h2). Qed.
Lemma lem3197287 {A : Type'} (FINITE' : type686 A) (FINITE'' : type686 A) (h1 : term55 A FINITE') (h2 : FINITE'' = (term61 A)) : term71 A FINITE'' FINITE'.
Proof. exact (fun a : A -> Prop => @lem3197286 A a FINITE' FINITE'' h1 h2). Qed.
Lemma lem3197288 {A : Type'} (FINITE' : type686 A) (FINITE'' : type686 A) (h1 : FINITE'' = (term61 A)) : term72 A FINITE'' FINITE'.
Proof. exact (fun h0 : term55 A FINITE' => @lem3197287 A FINITE' FINITE'' h0 h1). Qed.
Lemma lem3197289 {A : Type'} (FINITE' : type686 A) (h1 : FINITE' = (term61 A)) : term73 A FINITE'.
Proof. exact (fun FINITE'' : type686 A => @lem3197288 A FINITE'' FINITE' h1). Qed.
Lemma lem3197290 {A : Type'} (h1 : term74 A) : term74 A.
Proof. exact (h1). Qed.
Lemma lem3197291 {A : Type'} (FINITE' : type686 A) (h1 : term55 A FINITE') : term55 A FINITE'.
Proof. exact (h1). Qed.
Lemma lem3197292 {A : Type'} (FINITE' : type686 A) (FINITE'' : type686 A) (h1 : FINITE'' = (term61 A)) : term75 A FINITE'' FINITE'.
Proof. exact (@lem3197289 A FINITE'' h1 FINITE'). Qed.
Lemma lem3197293 {A : Type'} (FINITE' : type686 A) (FINITE'' : type686 A) : (term75 A FINITE' FINITE'') = (term72 A FINITE' FINITE'').
Proof. exact (eq_refl (term75 A FINITE' FINITE'')). Qed.
Lemma lem3197294 {A : Type'} (FINITE' : type686 A) (FINITE'' : type686 A) (h1 : FINITE'' = (term61 A)) : term72 A FINITE'' FINITE'.
Proof. exact (EQ_MP (@lem3197293 A FINITE'' FINITE') (@lem3197292 A FINITE' FINITE'' h1)). Qed.
Lemma lem3197295 {A : Type'} (FINITE' : type686 A) (FINITE'' : type686 A) (h1 : term55 A FINITE') (h2 : FINITE'' = (term61 A)) : term71 A FINITE'' FINITE'.
Proof. exact (@lem3197294 A FINITE' FINITE'' h2 (@lem3197291 A FINITE' h1)). Qed.
Lemma lem3197296 {A : Type'} (FINITE' : type686 A) (h1 : term74 A) : term76 A FINITE'.
Proof. exact (@lem3197290 A h1 FINITE'). Qed.
Lemma lem3197297 {A : Type'} (FINITE' : type686 A) : (term76 A FINITE') = (term77 A FINITE').
Proof. exact (eq_refl (term76 A FINITE')). Qed.
Lemma lem3197298 {A : Type'} (FINITE' : type686 A) (h1 : term74 A) : term77 A FINITE'.
Proof. exact (EQ_MP (@lem3197297 A FINITE') (@lem3197296 A FINITE' h1)). Qed.
Lemma lem3197299 {A : Type'} (FINITE' : type686 A) (FINITE'' : type686 A) (h1 : term74 A) : term78 A FINITE' FINITE''.
Proof. exact (@lem3197298 A FINITE' h1 FINITE''). Qed.
Lemma lem3197300 {A : Type'} (FINITE' : type686 A) (FINITE'' : type686 A) : (term78 A FINITE' FINITE'') = (term79 A FINITE' FINITE'').
Proof. exact (eq_refl (term78 A FINITE' FINITE'')). Qed.
Lemma lem3197301 {A : Type'} (FINITE' : type686 A) (FINITE'' : type686 A) (h1 : term74 A) : term79 A FINITE' FINITE''.
Proof. exact (EQ_MP (@lem3197300 A FINITE' FINITE'') (@lem3197299 A FINITE' FINITE'' h1)). Qed.
Lemma lem3197302 {A : Type'} (FINITE' : type686 A) (FINITE'' : type686 A) (h1 : term55 A FINITE') (h2 : term74 A) (h3 : FINITE'' = (term61 A)) : term80 A FINITE'' FINITE'.
Proof. exact (@lem3197301 A FINITE'' FINITE' h2 (@lem3197295 A FINITE' FINITE'' h1 h3)). Qed.
Lemma lem3197303 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term55 A FINITE') : term56 A FINITE' a.
Proof. exact (@lem3197291 A FINITE' h1 a). Qed.
Lemma lem3197304 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) : (term56 A FINITE' a) = (term54 A FINITE' a).
Proof. exact (eq_refl (term56 A FINITE' a)). Qed.
Lemma lem3197305 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term55 A FINITE') : term54 A FINITE' a.
Proof. exact (EQ_MP (@lem3197304 A FINITE' a) (@lem3197303 A a FINITE' h1)). Qed.
Lemma lem3197306 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (FINITE'' : type686 A) (h1 : term55 A FINITE') (h2 : term74 A) (h3 : FINITE'' = (term61 A)) : term81 A FINITE'' FINITE' a.
Proof. exact (@lem3197302 A FINITE' FINITE'' h1 h2 h3 a). Qed.
Lemma lem3197307 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (FINITE'' : type686 A) : (term81 A FINITE' FINITE'' a) = (term82 A FINITE' a FINITE'').
Proof. exact (eq_refl (term81 A FINITE' FINITE'' a)). Qed.
Lemma lem3197308 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (FINITE'' : type686 A) (h1 : term55 A FINITE') (h2 : term74 A) (h3 : FINITE'' = (term61 A)) : term82 A FINITE'' a FINITE'.
Proof. exact (EQ_MP (@lem3197307 A FINITE'' a FINITE') (@lem3197306 A a FINITE' FINITE'' h1 h2 h3)). Qed.
Lemma lem3197309 {A : Type'} (FINITE' : type686 A) (FINITE'' : type686 A) (a : A -> Prop) : term83 A FINITE' FINITE'' a.
Proof. exact (@lem51 (term53 A a FINITE'') (term53 A a FINITE') (FINITE'' a)). Qed.
Lemma lem3197310 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (FINITE'' : type686 A) (h1 : term55 A FINITE') (h2 : term74 A) (h3 : FINITE'' = (term61 A)) : term84 A FINITE'' FINITE' a.
Proof. exact (@lem3197309 A FINITE'' FINITE' a (@lem3197308 A a FINITE' FINITE'' h1 h2 h3)). Qed.
Lemma lem3197311 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (FINITE'' : type686 A) (h1 : term55 A FINITE') (h2 : term74 A) (h3 : FINITE'' = (term61 A)) : term85 A FINITE'' FINITE' a.
Proof. exact (@lem3197310 A a FINITE' FINITE'' h1 h2 h3 (@lem3197305 A a FINITE' h1)). Qed.
Lemma lem3197312 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term53 A a FINITE') : term53 A a FINITE'.
Proof. exact (h1). Qed.
Lemma lem3197313 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (FINITE'' : type686 A) (h1 : term55 A FINITE') (h2 : term74 A) (h3 : FINITE'' = (term61 A)) (h4 : term53 A a FINITE'') : FINITE' a.
Proof. exact (@lem3197311 A a FINITE' FINITE'' h1 h2 h3 (@lem3197312 A a FINITE'' h4)). Qed.
Lemma lem3197314 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (FINITE'' : type686 A) (h1 : term74 A) (h2 : FINITE'' = (term61 A)) (h3 : term53 A a FINITE'') : term57 A FINITE' a.
Proof. exact (fun h0 : term55 A FINITE' => @lem3197313 A FINITE' a FINITE'' h0 h1 h2 h3). Qed.
Lemma lem3197315 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term74 A) (h2 : FINITE' = (term61 A)) (h3 : term53 A a FINITE') : term63 A a.
Proof. exact (fun FINITE'' : type686 A => @lem3197314 A FINITE'' a FINITE' h1 h2 h3). Qed.
Lemma lem3197316 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : FINITE' = (term61 A)) : term66 A FINITE' a.
Proof. exact (@lem3197271 A FINITE' h1 a). Qed.
Lemma lem3197317 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) : (term66 A FINITE' a) = ((FINITE' a) = (term63 A a)).
Proof. exact (eq_refl (term66 A FINITE' a)). Qed.
Lemma lem3197318 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : FINITE' = (term61 A)) : (FINITE' a) = (term63 A a).
Proof. exact (EQ_MP (@lem3197317 A FINITE' a) (@lem3197316 A a FINITE' h1)). Qed.
Lemma lem3197319 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : FINITE' = (term61 A)) : (term63 A a) = (FINITE' a).
Proof. exact (SYM (@lem3197318 A a FINITE' h1)). Qed.
Lemma lem3197320 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term74 A) (h2 : FINITE' = (term61 A)) (h3 : term53 A a FINITE') : FINITE' a.
Proof. exact (EQ_MP (@lem3197319 A a FINITE' h2) (@lem3197315 A a FINITE' h1 h2 h3)). Qed.
Lemma lem3197321 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term74 A) (h2 : FINITE' = (term61 A)) : term54 A FINITE' a.
Proof. exact (fun h0 : term53 A a FINITE' => @lem3197320 A a FINITE' h1 h2 h0). Qed.
Lemma lem3197322 {A : Type'} (FINITE' : type686 A) (h1 : term74 A) (h2 : FINITE' = (term61 A)) : term55 A FINITE'.
Proof. exact (fun a : A -> Prop => @lem3197321 A a FINITE' h1 h2). Qed.
Lemma lem3197325 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) : (term86 A FINITE' a) = (term86 A FINITE' a).
Proof. exact (eq_refl (term86 A FINITE' a)). Qed.
Lemma lem3197326 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) : (term86 A FINITE' a) = (term53 A a FINITE').
Proof. exact (eq_refl (term86 A FINITE' a)). Qed.
Lemma lem3197327 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) : (term87 A FINITE' a) = (term87 A FINITE' a).
Proof. exact (eq_refl (term87 A FINITE' a)). Qed.
Lemma lem3197328 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) : ((term86 A FINITE' a) = (term86 A FINITE' a)) = ((term86 A FINITE' a) = (term53 A a FINITE')).
Proof. exact (MK_COMB (@lem3197327 A FINITE' a) (@lem3197326 A a FINITE')). Qed.
Lemma lem3197329 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) : (term86 A FINITE' a) = (term53 A a FINITE').
Proof. exact (EQ_MP (@lem3197328 A a FINITE') (@lem3197325 A FINITE' a)). Qed.
Lemma lem3197330 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3197331 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) : (term88 A FINITE' a) = (term89 A a FINITE').
Proof. exact (MK_COMB (@lem3197330) (@lem3197329 A a FINITE')). Qed.
Lemma lem3197332 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) : (FINITE' a) = (FINITE' a).
Proof. exact (eq_refl (FINITE' a)). Qed.
Lemma lem3197333 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) : (term90 A FINITE' a) = (term54 A FINITE' a).
Proof. exact (MK_COMB (@lem3197331 A a FINITE') (@lem3197332 A FINITE' a)). Qed.
Lemma lem3197334 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) : (term91 A a FINITE') = (term91 A a FINITE').
Proof. exact (eq_refl (term91 A a FINITE')). Qed.
Lemma lem3197335 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) : (term92 A FINITE' a) = (term93 A a FINITE').
Proof. exact (MK_COMB (@lem3197334 A a FINITE') (@lem3197329 A a FINITE')). Qed.
Lemma lem3197336 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) : (term94 A FINITE' a) = (term94 A FINITE' a).
Proof. exact (eq_refl (term94 A FINITE' a)). Qed.
Lemma lem3197337 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) : (term95 A FINITE' a) = (term96 A a FINITE').
Proof. exact (MK_COMB (@lem3197336 A FINITE' a) (@lem3197329 A a FINITE')). Qed.
Lemma lem3197338 {A : Type'} (FINITE' : type686 A) : (term97 A FINITE') = (term98 A FINITE').
Proof. exact (fun_ext (fun a : A -> Prop => @lem3197337 A a FINITE')). Qed.
Lemma lem3197339 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3197340 {A : Type'} (FINITE' : type686 A) : (term99 A FINITE') = (term100 A FINITE').
Proof. exact (MK_COMB (@lem3197339 A) (@lem3197338 A FINITE')). Qed.
Lemma lem3197341 {A : Type'} (FINITE' : type686 A) : (term101 A FINITE') = (term102 A FINITE').
Proof. exact (fun_ext (fun a : A -> Prop => @lem3197335 A a FINITE')). Qed.
Lemma lem3197342 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3197343 {A : Type'} (FINITE' : type686 A) : (term103 A FINITE') = (term104 A FINITE').
Proof. exact (MK_COMB (@lem3197342 A) (@lem3197341 A FINITE')). Qed.
Lemma lem3197344 {A : Type'} (FINITE' : type686 A) : (term105 A FINITE') = (term106 A FINITE').
Proof. exact (fun_ext (fun a : A -> Prop => @lem3197333 A FINITE' a)). Qed.
Lemma lem3197345 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3197346 {A : Type'} (FINITE' : type686 A) : (term107 A FINITE') = (term55 A FINITE').
Proof. exact (MK_COMB (@lem3197345 A) (@lem3197344 A FINITE')). Qed.
Lemma lem3197347 {A : Type'} (FINITE' : type686 A) : (term55 A FINITE') = (term107 A FINITE').
Proof. exact (SYM (@lem3197346 A FINITE')). Qed.
Lemma lem3197348 {A : Type'} (FINITE' : type686 A) (h1 : term74 A) (h2 : FINITE' = (term61 A)) : term107 A FINITE'.
Proof. exact (EQ_MP (@lem3197347 A FINITE') (@lem3197322 A FINITE' h1 h2)). Qed.
Lemma lem3197349 {A : Type'} (FINITE' : type686 A) (h1 : term74 A) : term108 A FINITE'.
Proof. exact (@lem3197290 A h1 (term109 A FINITE')). Qed.
Lemma lem3197350 {A : Type'} (FINITE' : type686 A) : (term108 A FINITE') = (term110 A FINITE').
Proof. exact (eq_refl (term108 A FINITE')). Qed.
Lemma lem3197351 {A : Type'} (FINITE' : type686 A) (h1 : term74 A) : term110 A FINITE'.
Proof. exact (EQ_MP (@lem3197350 A FINITE') (@lem3197349 A FINITE' h1)). Qed.
Lemma lem3197352 {A : Type'} (FINITE' : type686 A) (h1 : term74 A) : term111 A FINITE'.
Proof. exact (@lem3197351 A FINITE' h1 FINITE'). Qed.
Lemma lem3197353 {A : Type'} (FINITE' : type686 A) : (term111 A FINITE') = (term112 A FINITE').
Proof. exact (eq_refl (term111 A FINITE')). Qed.
Lemma lem3197354 {A : Type'} (FINITE' : type686 A) (h1 : term74 A) : term112 A FINITE'.
Proof. exact (EQ_MP (@lem3197353 A FINITE') (@lem3197352 A FINITE' h1)). Qed.
Lemma lem3197355 {A : Type'} (FINITE' : type686 A) (h1 : term74 A) (h2 : FINITE' = (term61 A)) : term104 A FINITE'.
Proof. exact (@lem3197354 A FINITE' h1 (@lem3197348 A FINITE' h1 h2)). Qed.
Lemma lem3197356 {A : Type'} (FINITE' : type686 A) : (term104 A FINITE') = (term103 A FINITE').
Proof. exact (SYM (@lem3197343 A FINITE')). Qed.
Lemma lem3197357 {A : Type'} (FINITE' : type686 A) (h1 : term74 A) (h2 : FINITE' = (term61 A)) : term103 A FINITE'.
Proof. exact (EQ_MP (@lem3197356 A FINITE') (@lem3197355 A FINITE' h1 h2)). Qed.
Lemma lem3197358 {A : Type'} (FINITE' : type686 A) (h1 : FINITE' = (term61 A)) : term113 A FINITE'.
Proof. exact (@lem3197289 A FINITE' h1 (term109 A FINITE')). Qed.
Lemma lem3197359 {A : Type'} (FINITE' : type686 A) : (term113 A FINITE') = (term114 A FINITE').
Proof. exact (eq_refl (term113 A FINITE')). Qed.
Lemma lem3197360 {A : Type'} (FINITE' : type686 A) (h1 : FINITE' = (term61 A)) : term114 A FINITE'.
Proof. exact (EQ_MP (@lem3197359 A FINITE') (@lem3197358 A FINITE' h1)). Qed.
Lemma lem3197361 {A : Type'} (FINITE' : type686 A) (h1 : term74 A) (h2 : FINITE' = (term61 A)) : term99 A FINITE'.
Proof. exact (@lem3197360 A FINITE' h2 (@lem3197357 A FINITE' h1 h2)). Qed.
Lemma lem3197362 {A : Type'} (FINITE' : type686 A) (h1 : term74 A) (h2 : FINITE' = (term61 A)) : term100 A FINITE'.
Proof. exact (EQ_MP (@lem3197340 A FINITE') (@lem3197361 A FINITE' h1 h2)). Qed.
Lemma lem3197363 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term74 A) (h2 : FINITE' = (term61 A)) : term56 A FINITE' a.
Proof. exact (@lem3197322 A FINITE' h1 h2 a). Qed.
Lemma lem3197364 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) : (term56 A FINITE' a) = (term54 A FINITE' a).
Proof. exact (eq_refl (term56 A FINITE' a)). Qed.
Lemma lem3197365 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term74 A) (h2 : FINITE' = (term61 A)) : term54 A FINITE' a.
Proof. exact (EQ_MP (@lem3197364 A FINITE' a) (@lem3197363 A a FINITE' h1 h2)). Qed.
Lemma lem3197366 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term74 A) (h2 : FINITE' = (term61 A)) : term115 A FINITE' a.
Proof. exact (@lem3197362 A FINITE' h1 h2 a). Qed.
Lemma lem3197367 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) : (term115 A FINITE' a) = (term96 A a FINITE').
Proof. exact (eq_refl (term115 A FINITE' a)). Qed.
Lemma lem3197368 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term74 A) (h2 : FINITE' = (term61 A)) : term96 A a FINITE'.
Proof. exact (EQ_MP (@lem3197367 A a FINITE') (@lem3197366 A a FINITE' h1 h2)). Qed.
Lemma lem3197369 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term74 A) (h2 : FINITE' = (term61 A)) : term116 A FINITE' a.
Proof. exact (conj (@lem3197368 A a FINITE' h1 h2) (@lem3197365 A a FINITE' h1 h2)). Qed.
Lemma lem3197370 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) : (term116 A FINITE' a) = ((FINITE' a) = (term53 A a FINITE')).
Proof. exact (@lem32 (FINITE' a) (term53 A a FINITE')). Qed.
Lemma lem3197371 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (h1 : term74 A) (h2 : FINITE' = (term61 A)) : (FINITE' a) = (term53 A a FINITE').
Proof. exact (EQ_MP (@lem3197370 A a FINITE') (@lem3197369 A a FINITE' h1 h2)). Qed.
Lemma lem3197376 {A : Type'} (FINITE' : type686 A) (h1 : term74 A) (h2 : FINITE' = (term61 A)) : term55 A FINITE'.
Proof. exact (fun a : A -> Prop => @lem3197321 A a FINITE' h1 h2). Qed.
Lemma lem3197377 {A : Type'} (FINITE' : type686 A) (h1 : term74 A) (h2 : FINITE' = (term61 A)) : term117 A FINITE'.
Proof. exact (fun a : A -> Prop => @lem3197371 A a FINITE' h1 h2). Qed.
Lemma lem3197378 {A : Type'} (FINITE' : type686 A) (h1 : term74 A) (h2 : FINITE' = (term61 A)) : term73 A FINITE'.
Proof. exact (fun FINITE'' : type686 A => @lem3197288 A FINITE'' FINITE' h2). Qed.
Lemma lem3197379 {A : Type'} (FINITE' : type686 A) (h1 : term74 A) (h2 : FINITE' = (term61 A)) : term49 A FINITE'.
Proof. exact (EQ_MP (@lem3197263 A FINITE') (@lem3197376 A FINITE' h1 h2)). Qed.
Lemma lem3197393 {A : Type'} (FINITE' : type686 A) : (term55 A FINITE') = (term49 A FINITE').
Proof. exact (SYM (@lem3197262 A FINITE')). Qed.
Lemma lem3197394 {A : Type'} (FINITE' : type686 A) : (term55 A FINITE') = (term49 A FINITE').
Proof. exact (@lem3197393 A FINITE'). Qed.
Lemma lem3197395 {A : Type'} (FINITE' : type686 A) : (term55 A FINITE') = (term49 A FINITE').
Proof. exact (@lem3197394 A FINITE'). Qed.
Lemma lem3197396 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3197397 {A : Type'} (FINITE' : type686 A) : (term118 A FINITE') = (term119 A FINITE').
Proof. exact (MK_COMB (@lem3197396) (@lem3197395 A FINITE')). Qed.
Lemma lem3197422 {A : Type'} (FINITE' : type686 A) (FINITE'' : type686 A) : (term71 A FINITE' FINITE'') = (term71 A FINITE' FINITE'').
Proof. exact (eq_refl (term71 A FINITE' FINITE'')). Qed.
Lemma lem3197423 {A : Type'} (FINITE' : type686 A) (FINITE'' : type686 A) : (term72 A FINITE' FINITE'') = (term120 A FINITE' FINITE'').
Proof. exact (MK_COMB (@lem3197397 A FINITE'') (@lem3197422 A FINITE' FINITE'')). Qed.
Lemma lem3197424 {A : Type'} (FINITE' : type686 A) : (term121 A FINITE') = (term122 A FINITE').
Proof. exact (fun_ext (fun FINITE'' : type686 A => @lem3197423 A FINITE' FINITE'')). Qed.
Lemma lem3197425 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3197426 {A : Type'} (FINITE' : type686 A) : (term73 A FINITE') = (term123 A FINITE').
Proof. exact (MK_COMB (@lem3197425 A) (@lem3197424 A FINITE')). Qed.
Lemma lem3197427 {A : Type'} (FINITE' : type686 A) (h1 : term74 A) (h2 : FINITE' = (term61 A)) : term123 A FINITE'.
Proof. exact (EQ_MP (@lem3197426 A FINITE') (@lem3197378 A FINITE' h1 h2)). Qed.
Lemma lem3197428 {A : Type'} (FINITE' : type686 A) (h1 : term74 A) (h2 : FINITE' = (term61 A)) : term124 A FINITE'.
Proof. exact (conj (@lem3197427 A FINITE' h1 h2) (@lem3197377 A FINITE' h1 h2)). Qed.
Lemma lem3197429 {A : Type'} (FINITE' : type686 A) (h1 : term74 A) (h2 : FINITE' = (term61 A)) : term125 A FINITE'.
Proof. exact (conj (@lem3197379 A FINITE' h1 h2) (@lem3197428 A FINITE' h1 h2)). Qed.
Lemma lem3197430 {A : Type'} (FINITE' : type686 A) (FINITE'' : type686 A) (h1 : term71 A FINITE' FINITE'') : term71 A FINITE' FINITE''.
Proof. exact (h1). Qed.
Lemma lem3197432 (A : Prop) (C : Prop) (B : Prop) (D : Prop) : term126 A C B D.
Proof. exact (fun h0 : term127 A B C D => @lem7129 A B C D h0). Qed.
Lemma lem3197434 {A : Type'} (a : A -> Prop) : term128 A a.
Proof. exact (@lem9120 (a = (@EMPTY A))). Qed.
Lemma lem3197435 {A : Type'} (a : A -> Prop) : (term128 A a) = (term129 A a).
Proof. exact (eq_refl (term128 A a)). Qed.
Lemma lem3197436 {A : Type'} (a : A -> Prop) : term129 A a.
Proof. exact (EQ_MP (@lem3197435 A a) (@lem3197434 A a)). Qed.
Lemma lem3197438 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term130 A P Q.
Proof. exact (fun h0 : term131 A P Q => @lem7400 A P Q h0). Qed.
Lemma lem3197439 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term130 A P Q.
Proof. exact (@lem3197438 A P Q). Qed.
Lemma lem3197440 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (FINITE'' : type686 A) : term132 A FINITE' a FINITE''.
Proof. exact (@lem3197439 A (term38 A a FINITE') (term38 A a FINITE'')). Qed.
Lemma lem3197441 {A : Type'} (a : A -> Prop) (x : A) (FINITE' : type686 A) : (term133 A a FINITE' x) = (term35 A a x FINITE').
Proof. exact (eq_refl (term133 A a FINITE' x)). Qed.
Lemma lem3197442 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3197443 {A : Type'} (a : A -> Prop) (x : A) (FINITE' : type686 A) : (term134 A a FINITE' x) = (term135 A a x FINITE').
Proof. exact (MK_COMB (@lem3197442) (@lem3197441 A a x FINITE')). Qed.
Lemma lem3197444 {A : Type'} (a : A -> Prop) (x : A) (FINITE' : type686 A) : (term133 A a FINITE' x) = (term35 A a x FINITE').
Proof. exact (eq_refl (term133 A a FINITE' x)). Qed.
Lemma lem3197445 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (x : A) (FINITE'' : type686 A) : (term136 A FINITE' a FINITE'' x) = (term137 A FINITE' a x FINITE'').
Proof. exact (MK_COMB (@lem3197443 A a x FINITE') (@lem3197444 A a x FINITE'')). Qed.
Lemma lem3197446 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (FINITE'' : type686 A) : (term138 A FINITE' a FINITE'') = (term139 A FINITE' a FINITE'').
Proof. exact (fun_ext (fun x : A => @lem3197445 A FINITE' a x FINITE'')). Qed.
Lemma lem3197447 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3197448 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (FINITE'' : type686 A) : (term140 A FINITE' a FINITE'') = (term141 A FINITE' a FINITE'').
Proof. exact (MK_COMB (@lem3197447 A) (@lem3197446 A FINITE' a FINITE'')). Qed.
Lemma lem3197449 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3197450 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (FINITE'' : type686 A) : (term142 A FINITE' a FINITE'') = (term143 A FINITE' a FINITE'').
Proof. exact (MK_COMB (@lem3197449) (@lem3197448 A FINITE' a FINITE'')). Qed.
Lemma lem3197451 {A : Type'} (a : A -> Prop) (x : A) (FINITE' : type686 A) : (term133 A a FINITE' x) = (term35 A a x FINITE').
Proof. exact (eq_refl (term133 A a FINITE' x)). Qed.
Lemma lem3197452 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) : (term144 A a FINITE') = (term38 A a FINITE').
Proof. exact (fun_ext (fun x : A => @lem3197451 A a x FINITE')). Qed.
Lemma lem3197453 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3197454 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) : (term145 A a FINITE') = (term37 A a FINITE').
Proof. exact (MK_COMB (@lem3197453 A) (@lem3197452 A a FINITE')). Qed.
Lemma lem3197455 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3197456 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) : (term146 A a FINITE') = (term147 A a FINITE').
Proof. exact (MK_COMB (@lem3197455) (@lem3197454 A a FINITE')). Qed.
Lemma lem3197457 {A : Type'} (a : A -> Prop) (x : A) (FINITE' : type686 A) : (term133 A a FINITE' x) = (term35 A a x FINITE').
Proof. exact (eq_refl (term133 A a FINITE' x)). Qed.
Lemma lem3197458 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) : (term144 A a FINITE') = (term38 A a FINITE').
Proof. exact (fun_ext (fun x : A => @lem3197457 A a x FINITE')). Qed.
Lemma lem3197459 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3197460 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) : (term145 A a FINITE') = (term37 A a FINITE').
Proof. exact (MK_COMB (@lem3197459 A) (@lem3197458 A a FINITE')). Qed.
Lemma lem3197461 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (FINITE'' : type686 A) : (term148 A FINITE' a FINITE'') = (term149 A FINITE' a FINITE'').
Proof. exact (MK_COMB (@lem3197456 A a FINITE') (@lem3197460 A a FINITE'')). Qed.
Lemma lem3197462 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (FINITE'' : type686 A) : (term132 A FINITE' a FINITE'') = (term150 A FINITE' a FINITE'').
Proof. exact (MK_COMB (@lem3197450 A FINITE' a FINITE'') (@lem3197461 A FINITE' a FINITE'')). Qed.
Lemma lem3197465 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term130 A P Q.
Proof. exact (fun h0 : term131 A P Q => @lem7400 A P Q h0). Qed.
Lemma lem3197466 {A : Type'} (P : type686 A) (Q : type686 A) : term151 A P Q.
Proof. exact (@lem3197465 (A -> Prop) P Q). Qed.
Lemma lem3197467 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (x : A) (FINITE'' : type686 A) : term152 A FINITE' a x FINITE''.
Proof. exact (@lem3197466 A (term36 A a x FINITE') (term36 A a x FINITE'')). Qed.
Lemma lem3197468 {A : Type'} (a : A -> Prop) (x : A) (FINITE' : type686 A) (s : A -> Prop) : (term153 A a x FINITE' s) = (term11 A a x FINITE' s).
Proof. exact (eq_refl (term153 A a x FINITE' s)). Qed.
Lemma lem3197469 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3197470 {A : Type'} (a : A -> Prop) (x : A) (FINITE' : type686 A) (s : A -> Prop) : (term154 A a x FINITE' s) = (term155 A a x FINITE' s).
Proof. exact (MK_COMB (@lem3197469) (@lem3197468 A a x FINITE' s)). Qed.
Lemma lem3197471 {A : Type'} (a : A -> Prop) (x : A) (FINITE' : type686 A) (s : A -> Prop) : (term153 A a x FINITE' s) = (term11 A a x FINITE' s).
Proof. exact (eq_refl (term153 A a x FINITE' s)). Qed.
Lemma lem3197472 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (x : A) (FINITE'' : type686 A) (s : A -> Prop) : (term156 A FINITE' a x FINITE'' s) = (term157 A FINITE' a x FINITE'' s).
Proof. exact (MK_COMB (@lem3197470 A a x FINITE' s) (@lem3197471 A a x FINITE'' s)). Qed.
Lemma lem3197473 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (x : A) (FINITE'' : type686 A) : (term158 A FINITE' a x FINITE'') = (term159 A FINITE' a x FINITE'').
Proof. exact (fun_ext (fun s : A -> Prop => @lem3197472 A FINITE' a x FINITE'' s)). Qed.
Lemma lem3197474 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3197475 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (x : A) (FINITE'' : type686 A) : (term160 A FINITE' a x FINITE'') = (term161 A FINITE' a x FINITE'').
Proof. exact (MK_COMB (@lem3197474 A) (@lem3197473 A FINITE' a x FINITE'')). Qed.
Lemma lem3197476 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3197477 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (x : A) (FINITE'' : type686 A) : (term162 A FINITE' a x FINITE'') = (term163 A FINITE' a x FINITE'').
Proof. exact (MK_COMB (@lem3197476) (@lem3197475 A FINITE' a x FINITE'')). Qed.
Lemma lem3197478 {A : Type'} (a : A -> Prop) (x : A) (FINITE' : type686 A) (s : A -> Prop) : (term153 A a x FINITE' s) = (term11 A a x FINITE' s).
Proof. exact (eq_refl (term153 A a x FINITE' s)). Qed.
Lemma lem3197479 {A : Type'} (a : A -> Prop) (x : A) (FINITE' : type686 A) : (term164 A a x FINITE') = (term36 A a x FINITE').
Proof. exact (fun_ext (fun s : A -> Prop => @lem3197478 A a x FINITE' s)). Qed.
Lemma lem3197480 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3197481 {A : Type'} (a : A -> Prop) (x : A) (FINITE' : type686 A) : (term165 A a x FINITE') = (term35 A a x FINITE').
Proof. exact (MK_COMB (@lem3197480 A) (@lem3197479 A a x FINITE')). Qed.
Lemma lem3197482 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3197483 {A : Type'} (a : A -> Prop) (x : A) (FINITE' : type686 A) : (term166 A a x FINITE') = (term135 A a x FINITE').
Proof. exact (MK_COMB (@lem3197482) (@lem3197481 A a x FINITE')). Qed.
Lemma lem3197484 {A : Type'} (a : A -> Prop) (x : A) (FINITE' : type686 A) (s : A -> Prop) : (term153 A a x FINITE' s) = (term11 A a x FINITE' s).
Proof. exact (eq_refl (term153 A a x FINITE' s)). Qed.
Lemma lem3197485 {A : Type'} (a : A -> Prop) (x : A) (FINITE' : type686 A) : (term164 A a x FINITE') = (term36 A a x FINITE').
Proof. exact (fun_ext (fun s : A -> Prop => @lem3197484 A a x FINITE' s)). Qed.
Lemma lem3197486 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3197487 {A : Type'} (a : A -> Prop) (x : A) (FINITE' : type686 A) : (term165 A a x FINITE') = (term35 A a x FINITE').
Proof. exact (MK_COMB (@lem3197486 A) (@lem3197485 A a x FINITE')). Qed.
Lemma lem3197488 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (x : A) (FINITE'' : type686 A) : (term167 A FINITE' a x FINITE'') = (term137 A FINITE' a x FINITE'').
Proof. exact (MK_COMB (@lem3197483 A a x FINITE') (@lem3197487 A a x FINITE'')). Qed.
Lemma lem3197489 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (x : A) (FINITE'' : type686 A) : (term152 A FINITE' a x FINITE'') = (term168 A FINITE' a x FINITE'').
Proof. exact (MK_COMB (@lem3197477 A FINITE' a x FINITE'') (@lem3197488 A FINITE' a x FINITE'')). Qed.
Lemma lem3197492 (A : Prop) (C : Prop) (B : Prop) (D : Prop) : term169 A C B D.
Proof. exact (fun h0 : term127 A B C D => @lem7058 A B C D h0). Qed.
Lemma lem3197494 {A : Type'} (a : A -> Prop) (x : A) (s : A -> Prop) : term170 A a x s.
Proof. exact (@lem9120 (a = (@INSERT A x s))). Qed.
Lemma lem3197495 {A : Type'} (a : A -> Prop) (x : A) (s : A -> Prop) : (term170 A a x s) = (term171 A a x s).
Proof. exact (eq_refl (term170 A a x s)). Qed.
Lemma lem3197496 {A : Type'} (a : A -> Prop) (x : A) (s : A -> Prop) : term171 A a x s.
Proof. exact (EQ_MP (@lem3197495 A a x s) (@lem3197494 A a x s)). Qed.
Lemma lem3197497 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (FINITE'' : type686 A) (h1 : term71 A FINITE' FINITE'') : term172 A FINITE' FINITE'' a.
Proof. exact (@lem3197430 A FINITE' FINITE'' h1 a). Qed.
Lemma lem3197498 {A : Type'} (FINITE' : type686 A) (FINITE'' : type686 A) (a : A -> Prop) : (term172 A FINITE' FINITE'' a) = (term70 A FINITE' FINITE'' a).
Proof. exact (eq_refl (term172 A FINITE' FINITE'' a)). Qed.
Lemma lem3197499 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (FINITE'' : type686 A) (h1 : term71 A FINITE' FINITE'') : term70 A FINITE' FINITE'' a.
Proof. exact (EQ_MP (@lem3197498 A FINITE' FINITE'' a) (@lem3197497 A a FINITE' FINITE'' h1)). Qed.
Lemma lem3197500 {A : Type'} (FINITE' : type686 A) (FINITE'' : type686 A) (a : A -> Prop) : (term70 A FINITE' FINITE'' a) = ((term70 A FINITE' FINITE'' a) = True).
Proof. exact (@lem7 (term70 A FINITE' FINITE'' a)). Qed.
Lemma lem3197503 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (FINITE'' : type686 A) (h1 : term71 A FINITE' FINITE'') : (term70 A FINITE' FINITE'' a) = True.
Proof. exact (EQ_MP (@lem3197500 A FINITE' FINITE'' a) (@lem3197499 A a FINITE' FINITE'' h1)). Qed.
Lemma lem3197504 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (FINITE'' : type686 A) (h1 : term71 A FINITE' FINITE'') : (term70 A FINITE' FINITE'' a) = True.
Proof. exact (@lem3197503 A a FINITE' FINITE'' h1). Qed.
Lemma lem3197505 {A : Type'} (s : A -> Prop) (FINITE' : type686 A) (FINITE'' : type686 A) (h1 : term71 A FINITE' FINITE'') : (term70 A FINITE' FINITE'' s) = True.
Proof. exact (@lem3197504 A s FINITE' FINITE'' h1). Qed.
Lemma lem3197506 {A : Type'} (s : A -> Prop) (FINITE' : type686 A) (FINITE'' : type686 A) (h1 : term71 A FINITE' FINITE'') : True = (term70 A FINITE' FINITE'' s).
Proof. exact (SYM (@lem3197505 A s FINITE' FINITE'' h1)). Qed.
Lemma lem3197507 {A : Type'} (s : A -> Prop) (FINITE' : type686 A) (FINITE'' : type686 A) (h1 : term71 A FINITE' FINITE'') : term70 A FINITE' FINITE'' s.
Proof. exact (EQ_MP (@lem3197506 A s FINITE' FINITE'' h1) (@lem0)). Qed.
Lemma lem3197508 {A : Type'} (a : A -> Prop) (x : A) (s : A -> Prop) (FINITE' : type686 A) (FINITE'' : type686 A) (h1 : term71 A FINITE' FINITE'') : term173 A a x FINITE' FINITE'' s.
Proof. exact (conj (@lem3197496 A a x s) (@lem3197507 A s FINITE' FINITE'' h1)). Qed.
Lemma lem3197510 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (x : A) (FINITE'' : type686 A) (s : A -> Prop) : term174 A FINITE' a x FINITE'' s.
Proof. exact (@lem3197492 (a = (@INSERT A x s)) (FINITE' s) (a = (@INSERT A x s)) (FINITE'' s)). Qed.
Lemma lem3197511 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (x : A) (FINITE'' : type686 A) (s : A -> Prop) : term174 A FINITE' a x FINITE'' s.
Proof. exact (@lem3197510 A FINITE' a x FINITE'' s). Qed.
Lemma lem3197512 {A : Type'} (a : A -> Prop) (x : A) (s : A -> Prop) (FINITE' : type686 A) (FINITE'' : type686 A) (h1 : term71 A FINITE' FINITE'') : term157 A FINITE' a x FINITE'' s.
Proof. exact (@lem3197511 A FINITE' a x FINITE'' s (@lem3197508 A a x s FINITE' FINITE'' h1)). Qed.
Lemma lem3197517 {A : Type'} (a : A -> Prop) (x : A) (FINITE' : type686 A) (FINITE'' : type686 A) (h1 : term71 A FINITE' FINITE'') : term161 A FINITE' a x FINITE''.
Proof. exact (fun s : A -> Prop => @lem3197512 A a x s FINITE' FINITE'' h1). Qed.
Lemma lem3197519 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (x : A) (FINITE'' : type686 A) : term168 A FINITE' a x FINITE''.
Proof. exact (EQ_MP (@lem3197489 A FINITE' a x FINITE'') (@lem3197467 A FINITE' a x FINITE'')). Qed.
Lemma lem3197520 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (x : A) (FINITE'' : type686 A) : term168 A FINITE' a x FINITE''.
Proof. exact (@lem3197519 A FINITE' a x FINITE''). Qed.
Lemma lem3197521 {A : Type'} (a : A -> Prop) (x : A) (FINITE' : type686 A) (FINITE'' : type686 A) (h1 : term71 A FINITE' FINITE'') : term137 A FINITE' a x FINITE''.
Proof. exact (@lem3197520 A FINITE' a x FINITE'' (@lem3197517 A a x FINITE' FINITE'' h1)). Qed.
Lemma lem3197526 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (FINITE'' : type686 A) (h1 : term71 A FINITE' FINITE'') : term141 A FINITE' a FINITE''.
Proof. exact (fun x : A => @lem3197521 A a x FINITE' FINITE'' h1). Qed.
Lemma lem3197528 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (FINITE'' : type686 A) : term150 A FINITE' a FINITE''.
Proof. exact (EQ_MP (@lem3197462 A FINITE' a FINITE'') (@lem3197440 A FINITE' a FINITE'')). Qed.
Lemma lem3197529 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (FINITE'' : type686 A) : term150 A FINITE' a FINITE''.
Proof. exact (@lem3197528 A FINITE' a FINITE''). Qed.
Lemma lem3197530 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (FINITE'' : type686 A) (h1 : term71 A FINITE' FINITE'') : term149 A FINITE' a FINITE''.
Proof. exact (@lem3197529 A FINITE' a FINITE'' (@lem3197526 A a FINITE' FINITE'' h1)). Qed.
Lemma lem3197531 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (FINITE'' : type686 A) (h1 : term71 A FINITE' FINITE'') : term175 A FINITE' a FINITE''.
Proof. exact (conj (@lem3197436 A a) (@lem3197530 A a FINITE' FINITE'' h1)). Qed.
Lemma lem3197533 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (FINITE'' : type686 A) : term176 A FINITE' a FINITE''.
Proof. exact (@lem3197432 (a = (@EMPTY A)) (term37 A a FINITE') (a = (@EMPTY A)) (term37 A a FINITE'')). Qed.
Lemma lem3197534 {A : Type'} (FINITE' : type686 A) (a : A -> Prop) (FINITE'' : type686 A) : term176 A FINITE' a FINITE''.
Proof. exact (@lem3197533 A FINITE' a FINITE''). Qed.
Lemma lem3197535 {A : Type'} (a : A -> Prop) (FINITE' : type686 A) (FINITE'' : type686 A) (h1 : term71 A FINITE' FINITE'') : term82 A FINITE' a FINITE''.
Proof. exact (@lem3197534 A FINITE' a FINITE'' (@lem3197531 A a FINITE' FINITE'' h1)). Qed.
Lemma lem3197540 {A : Type'} (FINITE' : type686 A) (FINITE'' : type686 A) (h1 : term71 A FINITE' FINITE'') : term80 A FINITE' FINITE''.
Proof. exact (fun a : A -> Prop => @lem3197535 A a FINITE' FINITE'' h1). Qed.
Lemma lem3197541 {A : Type'} (FINITE' : type686 A) (FINITE'' : type686 A) (h1 : term71 A FINITE' FINITE'') : (term71 A FINITE' FINITE'') = (term80 A FINITE' FINITE'').
Proof. exact (prop_ext (fun h2 : term71 A FINITE' FINITE'' => @lem3197540 A FINITE' FINITE'' h1) (fun h2 : term80 A FINITE' FINITE'' => @lem3197430 A FINITE' FINITE'' h1)). Qed.
Lemma lem3197542 {A : Type'} (FINITE' : type686 A) (FINITE'' : type686 A) (h1 : term71 A FINITE' FINITE'') : term80 A FINITE' FINITE''.
Proof. exact (EQ_MP (@lem3197541 A FINITE' FINITE'' h1) (@lem3197430 A FINITE' FINITE'' h1)). Qed.
Lemma lem3197543 {A : Type'} (FINITE' : type686 A) (FINITE'' : type686 A) : term79 A FINITE' FINITE''.
Proof. exact (fun h0 : term71 A FINITE' FINITE'' => @lem3197542 A FINITE' FINITE'' h0). Qed.
Lemma lem3197548 {A : Type'} (FINITE' : type686 A) : term77 A FINITE'.
Proof. exact (fun FINITE'' : type686 A => @lem3197543 A FINITE' FINITE''). Qed.
Lemma lem3197553 {A : Type'} : term74 A.
Proof. exact (fun FINITE' : type686 A => @lem3197548 A FINITE'). Qed.
Lemma lem3197554 {A : Type'} (FINITE' : type686 A) (h1 : FINITE' = (term61 A)) : (term74 A) = (term125 A FINITE').
Proof. exact (prop_ext (fun h2 : term74 A => @lem3197429 A FINITE' h2 h1) (fun h2 : term125 A FINITE' => @lem3197553 A)). Qed.
Lemma lem3197555 {A : Type'} (FINITE' : type686 A) (h1 : FINITE' = (term61 A)) : term125 A FINITE'.
Proof. exact (EQ_MP (@lem3197554 A FINITE' h1) (@lem3197553 A)). Qed.
Lemma lem3197556 {A : Type'} (FINITE' : type686 A) (h1 : FINITE' = (term61 A)) : FINITE' = (term61 A).
Proof. exact (h1). Qed.
Lemma lem3197557 {A : Type'} (FINITE' : type686 A) : term177 A FINITE'.
Proof. exact (fun h0 : FINITE' = (term61 A) => @lem3197555 A FINITE' h0). Qed.
Lemma lem3197558 {A : Type'} (FINITE' : type686 A) : term177 A FINITE'.
Proof. exact (@lem3197557 A FINITE'). Qed.
Lemma lem3197559 {A : Type'} (FINITE' : type686 A) (h1 : FINITE' = (term61 A)) : term125 A FINITE'.
Proof. exact (@lem3197558 A FINITE' (@lem3197556 A FINITE' h1)). Qed.
Lemma lem3197560 {A : Type'} : (@FINITE A) = (term61 A).
Proof. exact (@FINITE_def A). Qed.
Lemma lem3197561 {A : Type'} (FINITE' : type686 A) : term177 A FINITE'.
Proof. exact (fun h0 : FINITE' = (term61 A) => @lem3197559 A FINITE' h0). Qed.
Lemma lem3197562 {A : Type'} : term178 A.
Proof. exact (@lem3197561 A (@FINITE A)). Qed.
Lemma lem3197563 {A : Type'} : term179 A.
Proof. exact (@lem3197562 A (@lem3197560 A)). Qed.
