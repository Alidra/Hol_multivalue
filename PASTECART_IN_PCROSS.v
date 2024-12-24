Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PASTECART_IN_PCROSS_term_abbrevs.
Require Import IN_ELIM_PASTECART_THM_spec.
Require Import PCROSS_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem8004101 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) : term0 _141774 _141775 _141776 P.
Proof. exact (@lem8002422 _141774 _141775 _141776 P). Qed.
Lemma lem8004102 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) : (term0 _141774 _141775 _141776 P) = (term1 _141774 _141775 _141776 P).
Proof. exact (eq_refl (term0 _141774 _141775 _141776 P)). Qed.
Lemma lem8004103 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) : term1 _141774 _141775 _141776 P.
Proof. exact (EQ_MP (@lem8004102 _141774 _141775 _141776 P) (@lem8004101 _141774 _141775 _141776 P)). Qed.
Lemma lem8004104 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) : term2 _141774 _141775 _141776 P a.
Proof. exact (@lem8004103 _141774 _141775 _141776 P a). Qed.
Lemma lem8004105 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) : (term2 _141774 _141775 _141776 P a) = (term3 _141774 _141775 _141776 P a).
Proof. exact (eq_refl (term2 _141774 _141775 _141776 P a)). Qed.
Lemma lem8004106 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) : term3 _141774 _141775 _141776 P a.
Proof. exact (EQ_MP (@lem8004105 _141774 _141775 _141776 P a) (@lem8004104 _141774 _141775 _141776 P a)). Qed.
Lemma lem8004107 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : term4 _141774 _141775 _141776 P a b.
Proof. exact (@lem8004106 _141774 _141775 _141776 P a b). Qed.
Lemma lem8004108 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term4 _141774 _141775 _141776 P a b) = ((term5 _141774 _141775 _141776 a b P) = (P a b)).
Proof. exact (eq_refl (term4 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8004110 {A M N : Type'} (s : type24 A M) : term6 A M N s.
Proof. exact (@lem8003767 A M N s). Qed.
Lemma lem8004111 {A M N : Type'} (s : type24 A M) : (term6 A M N s) = (term7 A M N s).
Proof. exact (eq_refl (term6 A M N s)). Qed.
Lemma lem8004112 {A M N : Type'} (s : type24 A M) : term7 A M N s.
Proof. exact (EQ_MP (@lem8004111 A M N s) (@lem8004110 A M N s)). Qed.
Lemma lem8004113 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term8 A M N s t.
Proof. exact (@lem8004112 A M N s t). Qed.
Lemma lem8004114 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term8 A M N s t) = ((@PCROSS A M N s t) = (term9 A M N s t)).
Proof. exact (eq_refl (term8 A M N s t)). Qed.
Lemma lem8004135 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (@PCROSS A M N s t) = (term9 A M N s t).
Proof. exact (EQ_MP (@lem8004114 A M N s t) (@lem8004113 A M N s t)). Qed.
Lemma lem8004136 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (@PCROSS _141927 _141928 _141929 s t) = (term9 _141927 _141928 _141929 s t).
Proof. exact (@lem8004135 _141927 _141928 _141929 s t). Qed.
Lemma lem8004147 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (y : cart _141927 _141929) : (term10 _141927 _141928 _141929 x y) = (term10 _141927 _141928 _141929 x y).
Proof. exact (eq_refl (term10 _141927 _141928 _141929 x y)). Qed.
Lemma lem8004148 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (y : cart _141927 _141929) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term11 _141927 _141928 _141929 x y s t) = (term12 _141927 _141928 _141929 x y s t).
Proof. exact (MK_COMB (@lem8004147 _141927 _141928 _141929 x y) (@lem8004136 _141927 _141928 _141929 s t)). Qed.
Lemma lem8004150 {_141774 _141775 _141776 : Type'} (P : type22 _141774 _141775 _141776) (a : cart _141774 _141775) (b : cart _141774 _141776) : (term5 _141774 _141775 _141776 a b P) = (P a b).
Proof. exact (EQ_MP (@lem8004108 _141774 _141775 _141776 P a b) (@lem8004107 _141774 _141775 _141776 P a b)). Qed.
Lemma lem8004151 {_141927 _141928 _141929 : Type'} (P : type22 _141927 _141928 _141929) (a : cart _141927 _141928) (b : cart _141927 _141929) : (term5 _141927 _141928 _141929 a b P) = (P a b).
Proof. exact (@lem8004150 _141927 _141928 _141929 P a b). Qed.
Lemma lem8004152 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) (x : cart _141927 _141928) (y : cart _141927 _141929) : (term13 _141927 _141928 _141929 x y s t) = (term14 _141927 _141928 _141929 s t x y).
Proof. exact (@lem8004151 _141927 _141928 _141929 (term15 _141927 _141928 _141929 s t) x y). Qed.
Lemma lem8004153 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term16 _141927 _141928 _141929 s t x) = (term17 _141927 _141928 _141929 x s t).
Proof. exact (eq_refl (term16 _141927 _141928 _141929 s t x)). Qed.
Lemma lem8004154 {_141927 _141929 : Type'} (y : cart _141927 _141929) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem8004155 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) (y : cart _141927 _141929) : (term14 _141927 _141928 _141929 s t x y) = (term18 _141927 _141928 _141929 x s t y).
Proof. exact (MK_COMB (@lem8004153 _141927 _141928 _141929 x s t) (@lem8004154 _141927 _141929 y)). Qed.
Lemma lem8004156 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term18 _141927 _141928 _141929 x s t y) = (term19 _141927 _141928 _141929 x s y t).
Proof. exact (eq_refl (term18 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8004157 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term14 _141927 _141928 _141929 s t x y) = (term19 _141927 _141928 _141929 x s y t).
Proof. exact (TRANS (@lem8004155 _141927 _141928 _141929 x s t y) (@lem8004156 _141927 _141928 _141929 x s y t)). Qed.
Lemma lem8004158 {_141927 _141928 _141929 : Type'} (GEN_PVAR_361 : type2 _141927 _141928 _141929) : (@SETSPEC (cart _141927 (finite_sum _141928 _141929)) GEN_PVAR_361) = (@SETSPEC (cart _141927 (finite_sum _141928 _141929)) GEN_PVAR_361).
Proof. exact (eq_refl (@SETSPEC (cart _141927 (finite_sum _141928 _141929)) GEN_PVAR_361)). Qed.
Lemma lem8004159 {_141927 _141928 _141929 : Type'} (GEN_PVAR_361 : type2 _141927 _141928 _141929) (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term20 _141927 _141928 _141929 GEN_PVAR_361 s t x y) = (term21 _141927 _141928 _141929 GEN_PVAR_361 x s y t).
Proof. exact (MK_COMB (@lem8004158 _141927 _141928 _141929 GEN_PVAR_361) (@lem8004157 _141927 _141928 _141929 x s y t)). Qed.
Lemma lem8004160 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (y : cart _141927 _141929) : (@pastecart _141927 _141928 _141929 x y) = (@pastecart _141927 _141928 _141929 x y).
Proof. exact (eq_refl (@pastecart _141927 _141928 _141929 x y)). Qed.
Lemma lem8004161 {_141927 _141928 _141929 : Type'} (GEN_PVAR_361 : type2 _141927 _141928 _141929) (s : type24 _141927 _141928) (t : type24 _141927 _141929) (x : cart _141927 _141928) (y : cart _141927 _141929) : (term22 _141927 _141928 _141929 GEN_PVAR_361 s t x y) = (term23 _141927 _141928 _141929 GEN_PVAR_361 s t x y).
Proof. exact (MK_COMB (@lem8004159 _141927 _141928 _141929 GEN_PVAR_361 x s y t) (@lem8004160 _141927 _141928 _141929 x y)). Qed.
Lemma lem8004162 {_141927 _141928 _141929 : Type'} (GEN_PVAR_361 : type2 _141927 _141928 _141929) (s : type24 _141927 _141928) (t : type24 _141927 _141929) (x : cart _141927 _141928) : (term24 _141927 _141928 _141929 GEN_PVAR_361 s t x) = (term25 _141927 _141928 _141929 GEN_PVAR_361 s t x).
Proof. exact (fun_ext (fun y : cart _141927 _141929 => @lem8004161 _141927 _141928 _141929 GEN_PVAR_361 s t x y)). Qed.
Lemma lem8004163 {_141927 _141929 : Type'} : (@ex (cart _141927 _141929)) = (@ex (cart _141927 _141929)).
Proof. exact (eq_refl (@ex (cart _141927 _141929))). Qed.
Lemma lem8004164 {_141927 _141928 _141929 : Type'} (GEN_PVAR_361 : type2 _141927 _141928 _141929) (s : type24 _141927 _141928) (t : type24 _141927 _141929) (x : cart _141927 _141928) : (term26 _141927 _141928 _141929 GEN_PVAR_361 s t x) = (term27 _141927 _141928 _141929 GEN_PVAR_361 s t x).
Proof. exact (MK_COMB (@lem8004163 _141927 _141929) (@lem8004162 _141927 _141928 _141929 GEN_PVAR_361 s t x)). Qed.
Lemma lem8004165 {_141927 _141928 _141929 : Type'} (GEN_PVAR_361 : type2 _141927 _141928 _141929) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term28 _141927 _141928 _141929 GEN_PVAR_361 s t) = (term29 _141927 _141928 _141929 GEN_PVAR_361 s t).
Proof. exact (fun_ext (fun x : cart _141927 _141928 => @lem8004164 _141927 _141928 _141929 GEN_PVAR_361 s t x)). Qed.
Lemma lem8004166 {_141927 _141928 : Type'} : (@ex (cart _141927 _141928)) = (@ex (cart _141927 _141928)).
Proof. exact (eq_refl (@ex (cart _141927 _141928))). Qed.
Lemma lem8004167 {_141927 _141928 _141929 : Type'} (GEN_PVAR_361 : type2 _141927 _141928 _141929) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term30 _141927 _141928 _141929 GEN_PVAR_361 s t) = (term31 _141927 _141928 _141929 GEN_PVAR_361 s t).
Proof. exact (MK_COMB (@lem8004166 _141927 _141928) (@lem8004165 _141927 _141928 _141929 GEN_PVAR_361 s t)). Qed.
Lemma lem8004168 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term32 _141927 _141928 _141929 s t) = (term33 _141927 _141928 _141929 s t).
Proof. exact (fun_ext (fun GEN_PVAR_361 : type2 _141927 _141928 _141929 => @lem8004167 _141927 _141928 _141929 GEN_PVAR_361 s t)). Qed.
Lemma lem8004169 {_141927 _141928 _141929 : Type'} : (@GSPEC (cart _141927 (finite_sum _141928 _141929))) = (@GSPEC (cart _141927 (finite_sum _141928 _141929))).
Proof. exact (eq_refl (@GSPEC (cart _141927 (finite_sum _141928 _141929)))). Qed.
Lemma lem8004170 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term34 _141927 _141928 _141929 s t) = (term9 _141927 _141928 _141929 s t).
Proof. exact (MK_COMB (@lem8004169 _141927 _141928 _141929) (@lem8004168 _141927 _141928 _141929 s t)). Qed.
Lemma lem8004171 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (y : cart _141927 _141929) : (term10 _141927 _141928 _141929 x y) = (term10 _141927 _141928 _141929 x y).
Proof. exact (eq_refl (term10 _141927 _141928 _141929 x y)). Qed.
Lemma lem8004172 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (y : cart _141927 _141929) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term13 _141927 _141928 _141929 x y s t) = (term12 _141927 _141928 _141929 x y s t).
Proof. exact (MK_COMB (@lem8004171 _141927 _141928 _141929 x y) (@lem8004170 _141927 _141928 _141929 s t)). Qed.
Lemma lem8004173 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8004174 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (y : cart _141927 _141929) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term35 _141927 _141928 _141929 x y s t) = (term36 _141927 _141928 _141929 x y s t).
Proof. exact (MK_COMB (@lem8004173) (@lem8004172 _141927 _141928 _141929 x y s t)). Qed.
Lemma lem8004175 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term16 _141927 _141928 _141929 s t x) = (term17 _141927 _141928 _141929 x s t).
Proof. exact (eq_refl (term16 _141927 _141928 _141929 s t x)). Qed.
Lemma lem8004176 {_141927 _141929 : Type'} (y : cart _141927 _141929) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem8004177 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) (y : cart _141927 _141929) : (term14 _141927 _141928 _141929 s t x y) = (term18 _141927 _141928 _141929 x s t y).
Proof. exact (MK_COMB (@lem8004175 _141927 _141928 _141929 x s t) (@lem8004176 _141927 _141929 y)). Qed.
Lemma lem8004178 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term18 _141927 _141928 _141929 x s t y) = (term19 _141927 _141928 _141929 x s y t).
Proof. exact (eq_refl (term18 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8004179 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term14 _141927 _141928 _141929 s t x y) = (term19 _141927 _141928 _141929 x s y t).
Proof. exact (TRANS (@lem8004177 _141927 _141928 _141929 x s t y) (@lem8004178 _141927 _141928 _141929 x s y t)). Qed.
Lemma lem8004180 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : ((term13 _141927 _141928 _141929 x y s t) = (term14 _141927 _141928 _141929 s t x y)) = ((term12 _141927 _141928 _141929 x y s t) = (term19 _141927 _141928 _141929 x s y t)).
Proof. exact (MK_COMB (@lem8004174 _141927 _141928 _141929 x y s t) (@lem8004179 _141927 _141928 _141929 x s y t)). Qed.
Lemma lem8004181 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term12 _141927 _141928 _141929 x y s t) = (term19 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8004180 _141927 _141928 _141929 x s y t) (@lem8004152 _141927 _141928 _141929 s t x y)). Qed.
Lemma lem8004184 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term11 _141927 _141928 _141929 x y s t) = (term19 _141927 _141928 _141929 x s y t).
Proof. exact (TRANS (@lem8004148 _141927 _141928 _141929 x y s t) (@lem8004181 _141927 _141928 _141929 x s y t)). Qed.
Lemma lem8004185 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8004186 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term37 _141927 _141928 _141929 x y s t) = (term38 _141927 _141928 _141929 x s y t).
Proof. exact (MK_COMB (@lem8004185) (@lem8004184 _141927 _141928 _141929 x s y t)). Qed.
Lemma lem8004189 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term19 _141927 _141928 _141929 x s y t) = (term19 _141927 _141928 _141929 x s y t).
Proof. exact (eq_refl (term19 _141927 _141928 _141929 x s y t)). Qed.
Lemma lem8004190 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : ((term11 _141927 _141928 _141929 x y s t) = (term19 _141927 _141928 _141929 x s y t)) = ((term19 _141927 _141928 _141929 x s y t) = (term19 _141927 _141928 _141929 x s y t)).
Proof. exact (MK_COMB (@lem8004186 _141927 _141928 _141929 x s y t) (@lem8004189 _141927 _141928 _141929 x s y t)). Qed.
Lemma lem8004192 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8004193 (x : Prop) : (x = x) = True.
Proof. exact (@lem8004192 Prop x). Qed.
Lemma lem8004194 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : ((term19 _141927 _141928 _141929 x s y t) = (term19 _141927 _141928 _141929 x s y t)) = True.
Proof. exact (@lem8004193 (term19 _141927 _141928 _141929 x s y t)). Qed.
Lemma lem8004195 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : ((term11 _141927 _141928 _141929 x y s t) = (term19 _141927 _141928 _141929 x s y t)) = True.
Proof. exact (TRANS (@lem8004190 _141927 _141928 _141929 x s y t) (@lem8004194 _141927 _141928 _141929 x s y t)). Qed.
Lemma lem8004196 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term39 _141927 _141928 _141929 x s t) = (term40 _141927 _141929).
Proof. exact (fun_ext (fun y : cart _141927 _141929 => @lem8004195 _141927 _141928 _141929 x s y t)). Qed.
Lemma lem8004197 {_141927 _141929 : Type'} : (@all (cart _141927 _141929)) = (@all (cart _141927 _141929)).
Proof. exact (eq_refl (@all (cart _141927 _141929))). Qed.
Lemma lem8004198 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term41 _141927 _141928 _141929 x s t) = (term42 _141927 _141929).
Proof. exact (MK_COMB (@lem8004197 _141927 _141929) (@lem8004196 _141927 _141928 _141929 x s t)). Qed.
Lemma lem8004200 {A : Type'} (t : Prop) : (term43 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8004201 {_141927 _141929 : Type'} (t : Prop) : (term44 _141927 _141929 t) = t.
Proof. exact (@lem8004200 (cart _141927 _141929) t). Qed.
Lemma lem8004202 {_141927 _141929 : Type'} : (term42 _141927 _141929) = True.
Proof. exact (@lem8004201 _141927 _141929 True). Qed.
Lemma lem8004203 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term41 _141927 _141928 _141929 x s t) = True.
Proof. exact (TRANS (@lem8004198 _141927 _141928 _141929 x s t) (@lem8004202 _141927 _141929)). Qed.
Lemma lem8004204 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term45 _141927 _141928 _141929 s t) = (term40 _141927 _141928).
Proof. exact (fun_ext (fun x : cart _141927 _141928 => @lem8004203 _141927 _141928 _141929 x s t)). Qed.
Lemma lem8004205 {_141927 _141928 : Type'} : (@all (cart _141927 _141928)) = (@all (cart _141927 _141928)).
Proof. exact (eq_refl (@all (cart _141927 _141928))). Qed.
Lemma lem8004206 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term46 _141927 _141928 _141929 s t) = (term42 _141927 _141928).
Proof. exact (MK_COMB (@lem8004205 _141927 _141928) (@lem8004204 _141927 _141928 _141929 s t)). Qed.
Lemma lem8004208 {A : Type'} (t : Prop) : (term43 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8004209 {_141927 _141928 : Type'} (t : Prop) : (term44 _141927 _141928 t) = t.
Proof. exact (@lem8004208 (cart _141927 _141928) t). Qed.
Lemma lem8004210 {_141927 _141928 : Type'} : (term42 _141927 _141928) = True.
Proof. exact (@lem8004209 _141927 _141928 True). Qed.
Lemma lem8004211 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term46 _141927 _141928 _141929 s t) = True.
Proof. exact (TRANS (@lem8004206 _141927 _141928 _141929 s t) (@lem8004210 _141927 _141928)). Qed.
Lemma lem8004212 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : (term47 _141927 _141928 _141929 s) = (term48 _141927 _141929).
Proof. exact (fun_ext (fun t : type24 _141927 _141929 => @lem8004211 _141927 _141928 _141929 s t)). Qed.
Lemma lem8004213 {_141927 _141929 : Type'} : (@all ((cart _141927 _141929) -> Prop)) = (@all ((cart _141927 _141929) -> Prop)).
Proof. exact (eq_refl (@all ((cart _141927 _141929) -> Prop))). Qed.
Lemma lem8004214 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : (term49 _141927 _141928 _141929 s) = (term50 _141927 _141929).
Proof. exact (MK_COMB (@lem8004213 _141927 _141929) (@lem8004212 _141927 _141928 _141929 s)). Qed.
Lemma lem8004216 {A : Type'} (t : Prop) : (term43 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8004217 {_141927 _141929 : Type'} (t : Prop) : (term51 _141927 _141929 t) = t.
Proof. exact (@lem8004216 (type24 _141927 _141929) t). Qed.
Lemma lem8004218 {_141927 _141929 : Type'} : (term50 _141927 _141929) = True.
Proof. exact (@lem8004217 _141927 _141929 True). Qed.
Lemma lem8004219 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : (term49 _141927 _141928 _141929 s) = True.
Proof. exact (TRANS (@lem8004214 _141927 _141928 _141929 s) (@lem8004218 _141927 _141929)). Qed.
Lemma lem8004220 {_141927 _141928 _141929 : Type'} : (term52 _141927 _141928 _141929) = (term48 _141927 _141928).
Proof. exact (fun_ext (fun s : type24 _141927 _141928 => @lem8004219 _141927 _141928 _141929 s)). Qed.
Lemma lem8004221 {_141927 _141928 : Type'} : (@all ((cart _141927 _141928) -> Prop)) = (@all ((cart _141927 _141928) -> Prop)).
Proof. exact (eq_refl (@all ((cart _141927 _141928) -> Prop))). Qed.
Lemma lem8004222 {_141927 _141928 _141929 : Type'} : (term53 _141927 _141928 _141929) = (term50 _141927 _141928).
Proof. exact (MK_COMB (@lem8004221 _141927 _141928) (@lem8004220 _141927 _141928 _141929)). Qed.
Lemma lem8004224 {A : Type'} (t : Prop) : (term43 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8004225 {_141927 _141928 : Type'} (t : Prop) : (term51 _141927 _141928 t) = t.
Proof. exact (@lem8004224 (type24 _141927 _141928) t). Qed.
Lemma lem8004226 {_141927 _141928 : Type'} : (term50 _141927 _141928) = True.
Proof. exact (@lem8004225 _141927 _141928 True). Qed.
Lemma lem8004227 {_141927 _141928 _141929 : Type'} : (term53 _141927 _141928 _141929) = True.
Proof. exact (TRANS (@lem8004222 _141927 _141928 _141929) (@lem8004226 _141927 _141928)). Qed.
Lemma lem8004228 {_141927 _141928 _141929 : Type'} : True = (term53 _141927 _141928 _141929).
Proof. exact (SYM (@lem8004227 _141927 _141928 _141929)). Qed.
Lemma lem8004229 {_141927 _141928 _141929 : Type'} : term53 _141927 _141928 _141929.
Proof. exact (EQ_MP (@lem8004228 _141927 _141928 _141929) (@lem0)). Qed.
