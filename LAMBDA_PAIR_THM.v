Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LAMBDA_PAIR_THM_term_abbrevs.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm48805_spec.
Require Import thm48806_spec.
Require Import thm48811_spec.
Require Import thm48812_spec.
Require Import thm48920_spec.
Require Import thm51057_spec.
Require Import thm51073_spec.
Require Import thm51128_spec.
Require Import thm51159_spec.
Lemma lem51160 {_5153 _5154 : Type'} (a0 : _5154) (a1 : _5153) : a0 = (term0 _5153 _5154 a0 a1).
Proof. exact (@lem51128 _5154 _5153 a0 a1). Qed.
Lemma lem51161 {_5153 _5154 : Type'} (x : _5154) (y : _5153) : x = (term0 _5153 _5154 x y).
Proof. exact (@lem51160 _5153 _5154 x y). Qed.
Lemma lem51162 {_5153 _5154 : Type'} (a0 : _5154) (a1 : _5153) : a1 = (term1 _5153 _5154 a0 a1).
Proof. exact (@lem51159 _5154 _5153 a0 a1). Qed.
Lemma lem51163 {_5153 _5154 : Type'} (x : _5154) (y : _5153) : y = (term1 _5153 _5154 x y).
Proof. exact (@lem51162 _5153 _5154 x y). Qed.
Lemma lem51164 {_5154 : Type'} (x : _5154) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem51165 {_5154 : Type'} : (term2 _5154) = (term2 _5154).
Proof. exact (eq_refl (term2 _5154)). Qed.
Lemma lem51166 {_5153 _5154 : Type'} (x : _5154) (y : _5153) : (term3 _5154 x) = (term4 _5153 _5154 x y).
Proof. exact (MK_COMB (@lem51165 _5154) (@lem51161 _5153 _5154 x y)). Qed.
Lemma lem51167 {_5153 _5154 : Type'} (x : _5154) (y : _5153) : (term4 _5153 _5154 x y) = (term0 _5153 _5154 x y).
Proof. exact (eq_refl (term4 _5153 _5154 x y)). Qed.
Lemma lem51168 {_5154 : Type'} (x : _5154) : (term5 _5154 x) = (term5 _5154 x).
Proof. exact (eq_refl (term5 _5154 x)). Qed.
Lemma lem51169 {_5153 _5154 : Type'} (x : _5154) (y : _5153) : ((term3 _5154 x) = (term4 _5153 _5154 x y)) = ((term3 _5154 x) = (term0 _5153 _5154 x y)).
Proof. exact (MK_COMB (@lem51168 _5154 x) (@lem51167 _5153 _5154 x y)). Qed.
Lemma lem51170 {_5154 : Type'} (x : _5154) : (term3 _5154 x) = x.
Proof. exact (eq_refl (term3 _5154 x)). Qed.
Lemma lem51171 {_5154 : Type'} : (@eq _5154) = (@eq _5154).
Proof. exact (eq_refl (@eq _5154)). Qed.
Lemma lem51172 {_5154 : Type'} (x : _5154) : (term5 _5154 x) = (@eq _5154 x).
Proof. exact (MK_COMB (@lem51171 _5154) (@lem51170 _5154 x)). Qed.
Lemma lem51173 {_5153 _5154 : Type'} (x : _5154) (y : _5153) : (term0 _5153 _5154 x y) = (term0 _5153 _5154 x y).
Proof. exact (eq_refl (term0 _5153 _5154 x y)). Qed.
Lemma lem51174 {_5153 _5154 : Type'} (x : _5154) (y : _5153) : ((term3 _5154 x) = (term0 _5153 _5154 x y)) = (x = (term0 _5153 _5154 x y)).
Proof. exact (MK_COMB (@lem51172 _5154 x) (@lem51173 _5153 _5154 x y)). Qed.
Lemma lem51175 {_5153 _5154 : Type'} (x : _5154) (y : _5153) : ((term3 _5154 x) = (term4 _5153 _5154 x y)) = (x = (term0 _5153 _5154 x y)).
Proof. exact (TRANS (@lem51169 _5153 _5154 x y) (@lem51174 _5153 _5154 x y)). Qed.
Lemma lem51176 {_5153 _5154 : Type'} (x : _5154) (y : _5153) : x = (term0 _5153 _5154 x y).
Proof. exact (EQ_MP (@lem51175 _5153 _5154 x y) (@lem51166 _5153 _5154 x y)). Qed.
Lemma lem51177 {_5154 : Type'} (x : _5154) : (@eq _5154 x) = (@eq _5154 x).
Proof. exact (eq_refl (@eq _5154 x)). Qed.
Lemma lem51178 {_5153 _5154 : Type'} (x : _5154) (y : _5153) : (x = x) = (x = (term0 _5153 _5154 x y)).
Proof. exact (MK_COMB (@lem51177 _5154 x) (@lem51176 _5153 _5154 x y)). Qed.
Lemma lem51179 {_5153 _5154 : Type'} (x : _5154) (y : _5153) : x = (term0 _5153 _5154 x y).
Proof. exact (EQ_MP (@lem51178 _5153 _5154 x y) (@lem51164 _5154 x)). Qed.
Lemma lem51180 {_5153 : Type'} (y : _5153) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem51181 {_5153 : Type'} : (term2 _5153) = (term2 _5153).
Proof. exact (eq_refl (term2 _5153)). Qed.
Lemma lem51182 {_5153 _5154 : Type'} (x : _5154) (y : _5153) : (term3 _5153 y) = (term6 _5153 _5154 x y).
Proof. exact (MK_COMB (@lem51181 _5153) (@lem51163 _5153 _5154 x y)). Qed.
Lemma lem51183 {_5153 _5154 : Type'} (x : _5154) (y : _5153) : (term6 _5153 _5154 x y) = (term1 _5153 _5154 x y).
Proof. exact (eq_refl (term6 _5153 _5154 x y)). Qed.
Lemma lem51184 {_5153 : Type'} (y : _5153) : (term5 _5153 y) = (term5 _5153 y).
Proof. exact (eq_refl (term5 _5153 y)). Qed.
Lemma lem51185 {_5153 _5154 : Type'} (x : _5154) (y : _5153) : ((term3 _5153 y) = (term6 _5153 _5154 x y)) = ((term3 _5153 y) = (term1 _5153 _5154 x y)).
Proof. exact (MK_COMB (@lem51184 _5153 y) (@lem51183 _5153 _5154 x y)). Qed.
Lemma lem51186 {_5153 : Type'} (y : _5153) : (term3 _5153 y) = y.
Proof. exact (eq_refl (term3 _5153 y)). Qed.
Lemma lem51187 {_5153 : Type'} : (@eq _5153) = (@eq _5153).
Proof. exact (eq_refl (@eq _5153)). Qed.
Lemma lem51188 {_5153 : Type'} (y : _5153) : (term5 _5153 y) = (@eq _5153 y).
Proof. exact (MK_COMB (@lem51187 _5153) (@lem51186 _5153 y)). Qed.
Lemma lem51189 {_5153 _5154 : Type'} (x : _5154) (y : _5153) : (term1 _5153 _5154 x y) = (term1 _5153 _5154 x y).
Proof. exact (eq_refl (term1 _5153 _5154 x y)). Qed.
Lemma lem51190 {_5153 _5154 : Type'} (x : _5154) (y : _5153) : ((term3 _5153 y) = (term1 _5153 _5154 x y)) = (y = (term1 _5153 _5154 x y)).
Proof. exact (MK_COMB (@lem51188 _5153 y) (@lem51189 _5153 _5154 x y)). Qed.
Lemma lem51191 {_5153 _5154 : Type'} (x : _5154) (y : _5153) : ((term3 _5153 y) = (term6 _5153 _5154 x y)) = (y = (term1 _5153 _5154 x y)).
Proof. exact (TRANS (@lem51185 _5153 _5154 x y) (@lem51190 _5153 _5154 x y)). Qed.
Lemma lem51192 {_5153 _5154 : Type'} (x : _5154) (y : _5153) : y = (term1 _5153 _5154 x y).
Proof. exact (EQ_MP (@lem51191 _5153 _5154 x y) (@lem51182 _5153 _5154 x y)). Qed.
Lemma lem51193 {_5153 : Type'} (y : _5153) : (@eq _5153 y) = (@eq _5153 y).
Proof. exact (eq_refl (@eq _5153 y)). Qed.
Lemma lem51194 {_5153 _5154 : Type'} (x : _5154) (y : _5153) : (y = y) = (y = (term1 _5153 _5154 x y)).
Proof. exact (MK_COMB (@lem51193 _5153 y) (@lem51192 _5153 _5154 x y)). Qed.
Lemma lem51195 {_5153 _5154 : Type'} (x : _5154) (y : _5153) : y = (term1 _5153 _5154 x y).
Proof. exact (EQ_MP (@lem51194 _5153 _5154 x y) (@lem51180 _5153 y)). Qed.
Lemma lem51196 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) : (term7 _5146 _5153 _5154 t) = (term7 _5146 _5153 _5154 t).
Proof. exact (eq_refl (term7 _5146 _5153 _5154 t)). Qed.
Lemma lem51197 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (x : _5154) (y : _5153) : (term8 _5146 _5153 _5154 t x) = (term9 _5146 _5153 _5154 t x y).
Proof. exact (MK_COMB (@lem51196 _5146 _5153 _5154 t) (@lem51179 _5153 _5154 x y)). Qed.
Lemma lem51198 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (x : _5154) (y : _5153) : (term9 _5146 _5153 _5154 t x y) = (term10 _5146 _5153 _5154 t x y).
Proof. exact (eq_refl (term9 _5146 _5153 _5154 t x y)). Qed.
Lemma lem51199 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (x : _5154) : (term11 _5146 _5153 _5154 t x) = (term11 _5146 _5153 _5154 t x).
Proof. exact (eq_refl (term11 _5146 _5153 _5154 t x)). Qed.
Lemma lem51200 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (x : _5154) (y : _5153) : ((term8 _5146 _5153 _5154 t x) = (term9 _5146 _5153 _5154 t x y)) = ((term8 _5146 _5153 _5154 t x) = (term10 _5146 _5153 _5154 t x y)).
Proof. exact (MK_COMB (@lem51199 _5146 _5153 _5154 t x) (@lem51198 _5146 _5153 _5154 t x y)). Qed.
Lemma lem51201 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (x : _5154) : (term8 _5146 _5153 _5154 t x) = (term12 _5146 _5153 _5154 t x).
Proof. exact (eq_refl (term8 _5146 _5153 _5154 t x)). Qed.
Lemma lem51202 {_5146 _5153 : Type'} : (@eq (_5153 -> _5146)) = (@eq (_5153 -> _5146)).
Proof. exact (eq_refl (@eq (_5153 -> _5146))). Qed.
Lemma lem51203 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (x : _5154) : (term11 _5146 _5153 _5154 t x) = (term13 _5146 _5153 _5154 t x).
Proof. exact (MK_COMB (@lem51202 _5146 _5153) (@lem51201 _5146 _5153 _5154 t x)). Qed.
Lemma lem51204 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (x : _5154) (y : _5153) : (term10 _5146 _5153 _5154 t x y) = (term10 _5146 _5153 _5154 t x y).
Proof. exact (eq_refl (term10 _5146 _5153 _5154 t x y)). Qed.
Lemma lem51205 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (x : _5154) (y : _5153) : ((term8 _5146 _5153 _5154 t x) = (term10 _5146 _5153 _5154 t x y)) = ((term12 _5146 _5153 _5154 t x) = (term10 _5146 _5153 _5154 t x y)).
Proof. exact (MK_COMB (@lem51203 _5146 _5153 _5154 t x) (@lem51204 _5146 _5153 _5154 t x y)). Qed.
Lemma lem51206 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (x : _5154) (y : _5153) : ((term8 _5146 _5153 _5154 t x) = (term9 _5146 _5153 _5154 t x y)) = ((term12 _5146 _5153 _5154 t x) = (term10 _5146 _5153 _5154 t x y)).
Proof. exact (TRANS (@lem51200 _5146 _5153 _5154 t x y) (@lem51205 _5146 _5153 _5154 t x y)). Qed.
Lemma lem51207 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (x : _5154) (y : _5153) : (term12 _5146 _5153 _5154 t x) = (term10 _5146 _5153 _5154 t x y).
Proof. exact (EQ_MP (@lem51206 _5146 _5153 _5154 t x y) (@lem51197 _5146 _5153 _5154 t x y)). Qed.
Lemma lem51208 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (x : _5154) (y : _5153) : (term14 _5146 _5153 _5154 t x y) = (term15 _5146 _5153 _5154 t x y).
Proof. exact (MK_COMB (@lem51207 _5146 _5153 _5154 t x y) (@lem51195 _5153 _5154 x y)). Qed.
Lemma lem51209 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (x : _5154) (y : _5153) : (term15 _5146 _5153 _5154 t x y) = (term16 _5146 _5153 _5154 t x y).
Proof. exact (eq_refl (term15 _5146 _5153 _5154 t x y)). Qed.
Lemma lem51210 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (x : _5154) (y : _5153) : (term17 _5146 _5153 _5154 t x y) = (term17 _5146 _5153 _5154 t x y).
Proof. exact (eq_refl (term17 _5146 _5153 _5154 t x y)). Qed.
Lemma lem51211 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (x : _5154) (y : _5153) : ((term14 _5146 _5153 _5154 t x y) = (term15 _5146 _5153 _5154 t x y)) = ((term14 _5146 _5153 _5154 t x y) = (term16 _5146 _5153 _5154 t x y)).
Proof. exact (MK_COMB (@lem51210 _5146 _5153 _5154 t x y) (@lem51209 _5146 _5153 _5154 t x y)). Qed.
Lemma lem51212 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (x : _5154) (y : _5153) : (term14 _5146 _5153 _5154 t x y) = (term18 _5146 _5153 _5154 t x y).
Proof. exact (eq_refl (term14 _5146 _5153 _5154 t x y)). Qed.
Lemma lem51213 {_5146 : Type'} : (@eq _5146) = (@eq _5146).
Proof. exact (eq_refl (@eq _5146)). Qed.
Lemma lem51214 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (x : _5154) (y : _5153) : (term17 _5146 _5153 _5154 t x y) = (term19 _5146 _5153 _5154 t x y).
Proof. exact (MK_COMB (@lem51213 _5146) (@lem51212 _5146 _5153 _5154 t x y)). Qed.
Lemma lem51215 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (x : _5154) (y : _5153) : (term16 _5146 _5153 _5154 t x y) = (term16 _5146 _5153 _5154 t x y).
Proof. exact (eq_refl (term16 _5146 _5153 _5154 t x y)). Qed.
Lemma lem51216 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (x : _5154) (y : _5153) : ((term14 _5146 _5153 _5154 t x y) = (term16 _5146 _5153 _5154 t x y)) = ((term18 _5146 _5153 _5154 t x y) = (term16 _5146 _5153 _5154 t x y)).
Proof. exact (MK_COMB (@lem51214 _5146 _5153 _5154 t x y) (@lem51215 _5146 _5153 _5154 t x y)). Qed.
Lemma lem51217 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (x : _5154) (y : _5153) : ((term14 _5146 _5153 _5154 t x y) = (term15 _5146 _5153 _5154 t x y)) = ((term18 _5146 _5153 _5154 t x y) = (term16 _5146 _5153 _5154 t x y)).
Proof. exact (TRANS (@lem51211 _5146 _5153 _5154 t x y) (@lem51216 _5146 _5153 _5154 t x y)). Qed.
Lemma lem51218 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (x : _5154) (y : _5153) : (term18 _5146 _5153 _5154 t x y) = (term16 _5146 _5153 _5154 t x y).
Proof. exact (EQ_MP (@lem51217 _5146 _5153 _5154 t x y) (@lem51208 _5146 _5153 _5154 t x y)). Qed.
Lemma lem51219 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (x : _5154) (y : _5153) : (term16 _5146 _5153 _5154 t x y) = (term18 _5146 _5153 _5154 t x y).
Proof. exact (SYM (@lem51218 _5146 _5153 _5154 t x y)). Qed.
Lemma lem51220 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (x : _5154) (y : _5153) : (term20 _5146 _5153 _5154 t x y) = (term16 _5146 _5153 _5154 t x y).
Proof. exact (eq_refl (term20 _5146 _5153 _5154 t x y)). Qed.
Lemma lem51221 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (x : _5154) (y : _5153) : (term20 _5146 _5153 _5154 t x y) = (term18 _5146 _5153 _5154 t x y).
Proof. exact (TRANS (@lem51220 _5146 _5153 _5154 t x y) (@lem51219 _5146 _5153 _5154 t x y)). Qed.
Lemma lem51222 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (x : _5154) : term21 _5146 _5153 _5154 t x.
Proof. exact (fun y : _5153 => @lem51221 _5146 _5153 _5154 t x y). Qed.
Lemma lem51223 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) : term22 _5146 _5153 _5154 t.
Proof. exact (fun x : _5154 => @lem51222 _5146 _5153 _5154 t x). Qed.
Lemma lem51224 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) : term23 _5146 _5153 _5154 t.
Proof. exact (ex_intro (term24 _5146 _5153 _5154 t) (term25 _5146 _5153 _5154 t) (@lem51223 _5146 _5153 _5154 t)). Qed.
Lemma lem51226 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem51227 {_5146 : Type'} (a : _5146) (b : _5146) : (a = b) = (@GEQ _5146 a b).
Proof. exact (@lem51226 _5146 a b). Qed.
Lemma lem51228 {_5146 _5153 _5154 : Type'} (_1404 : type1228 _5146 _5153 _5154) (t : type1228 _5146 _5153 _5154) (x : _5154) (y : _5153) : ((term18 _5146 _5153 _5154 _1404 x y) = (term18 _5146 _5153 _5154 t x y)) = (term26 _5146 _5153 _5154 _1404 t x y).
Proof. exact (@lem51227 _5146 (term18 _5146 _5153 _5154 _1404 x y) (term18 _5146 _5153 _5154 t x y)). Qed.
Lemma lem51229 {_5146 _5153 _5154 : Type'} (_1404 : type1228 _5146 _5153 _5154) (t : type1228 _5146 _5153 _5154) (x : _5154) : (term27 _5146 _5153 _5154 _1404 t x) = (term28 _5146 _5153 _5154 _1404 t x).
Proof. exact (fun_ext (fun y : _5153 => @lem51228 _5146 _5153 _5154 _1404 t x y)). Qed.
Lemma lem51230 {_5153 : Type'} : (@all _5153) = (@all _5153).
Proof. exact (eq_refl (@all _5153)). Qed.
Lemma lem51231 {_5146 _5153 _5154 : Type'} (_1404 : type1228 _5146 _5153 _5154) (t : type1228 _5146 _5153 _5154) (x : _5154) : (term29 _5146 _5153 _5154 _1404 t x) = (term30 _5146 _5153 _5154 _1404 t x).
Proof. exact (MK_COMB (@lem51230 _5153) (@lem51229 _5146 _5153 _5154 _1404 t x)). Qed.
Lemma lem51232 {_5146 _5153 _5154 : Type'} (_1404 : type1228 _5146 _5153 _5154) (t : type1228 _5146 _5153 _5154) : (term31 _5146 _5153 _5154 _1404 t) = (term32 _5146 _5153 _5154 _1404 t).
Proof. exact (fun_ext (fun x : _5154 => @lem51231 _5146 _5153 _5154 _1404 t x)). Qed.
Lemma lem51233 {_5154 : Type'} : (@all _5154) = (@all _5154).
Proof. exact (eq_refl (@all _5154)). Qed.
Lemma lem51234 {_5146 _5153 _5154 : Type'} (_1404 : type1228 _5146 _5153 _5154) (t : type1228 _5146 _5153 _5154) : (term33 _5146 _5153 _5154 _1404 t) = (term34 _5146 _5153 _5154 _1404 t).
Proof. exact (MK_COMB (@lem51233 _5154) (@lem51232 _5146 _5153 _5154 _1404 t)). Qed.
Lemma lem51235 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) : (term24 _5146 _5153 _5154 t) = (term35 _5146 _5153 _5154 t).
Proof. exact (fun_ext (fun _1404 : type1228 _5146 _5153 _5154 => @lem51234 _5146 _5153 _5154 _1404 t)). Qed.
Lemma lem51236 {_5146 _5153 _5154 : Type'} : (@ex ((prod _5154 _5153) -> _5146)) = (@ex ((prod _5154 _5153) -> _5146)).
Proof. exact (eq_refl (@ex ((prod _5154 _5153) -> _5146))). Qed.
Lemma lem51237 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) : (term23 _5146 _5153 _5154 t) = (term36 _5146 _5153 _5154 t).
Proof. exact (MK_COMB (@lem51236 _5146 _5153 _5154) (@lem51235 _5146 _5153 _5154 t)). Qed.
Lemma lem51238 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) : term36 _5146 _5153 _5154 t.
Proof. exact (EQ_MP (@lem51237 _5146 _5153 _5154 t) (@lem51224 _5146 _5153 _5154 t)). Qed.
Lemma lem51240 {_5076 : Type'} (P : _5076 -> Prop) : term37 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem51241 {_5146 _5153 _5154 : Type'} (P : type333 _5146 _5153 _5154) : term38 _5146 _5153 _5154 P.
Proof. exact (@lem51240 (type1228 _5146 _5153 _5154) P). Qed.
Lemma lem51242 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) : term39 _5146 _5153 _5154 t.
Proof. exact (@lem51241 _5146 _5153 _5154 (term35 _5146 _5153 _5154 t)). Qed.
Lemma lem51243 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) : term40 _5146 _5153 _5154 t.
Proof. exact (@lem51242 _5146 _5153 _5154 t (@lem51238 _5146 _5153 _5154 t)). Qed.
Lemma lem51244 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) : (term40 _5146 _5153 _5154 t) = (term41 _5146 _5153 _5154 t).
Proof. exact (eq_refl (term40 _5146 _5153 _5154 t)). Qed.
Lemma lem51245 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) : term41 _5146 _5153 _5154 t.
Proof. exact (EQ_MP (@lem51244 _5146 _5153 _5154 t) (@lem51243 _5146 _5153 _5154 t)). Qed.
Lemma lem51246 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (x : _5154) : term42 _5146 _5153 _5154 t x.
Proof. exact (@lem51245 _5146 _5153 _5154 t x). Qed.
Lemma lem51247 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (x : _5154) : (term42 _5146 _5153 _5154 t x) = (term43 _5146 _5153 _5154 t x).
Proof. exact (eq_refl (term42 _5146 _5153 _5154 t x)). Qed.
Lemma lem51248 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (x : _5154) : term43 _5146 _5153 _5154 t x.
Proof. exact (EQ_MP (@lem51247 _5146 _5153 _5154 t x) (@lem51246 _5146 _5153 _5154 t x)). Qed.
Lemma lem51249 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (x : _5154) (y : _5153) : term44 _5146 _5153 _5154 t x y.
Proof. exact (@lem51248 _5146 _5153 _5154 t x y). Qed.
Lemma lem51250 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (x : _5154) (y : _5153) : (term44 _5146 _5153 _5154 t x y) = (term45 _5146 _5153 _5154 t x y).
Proof. exact (eq_refl (term44 _5146 _5153 _5154 t x y)). Qed.
Lemma lem51251 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (x : _5154) (y : _5153) : term45 _5146 _5153 _5154 t x y.
Proof. exact (EQ_MP (@lem51250 _5146 _5153 _5154 t x y) (@lem51249 _5146 _5153 _5154 t x y)). Qed.
Lemma lem51253 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem51254 {_5146 : Type'} (a : _5146) (b : _5146) : (@GEQ _5146 a b) = (a = b).
Proof. exact (@lem51253 _5146 a b). Qed.
Lemma lem51255 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (x : _5154) (y : _5153) : (term45 _5146 _5153 _5154 t x y) = ((term46 _5146 _5153 _5154 t x y) = (term18 _5146 _5153 _5154 t x y)).
Proof. exact (@lem51254 _5146 (term46 _5146 _5153 _5154 t x y) (term18 _5146 _5153 _5154 t x y)). Qed.
Lemma lem51256 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (x : _5154) (y : _5153) : (term46 _5146 _5153 _5154 t x y) = (term18 _5146 _5153 _5154 t x y).
Proof. exact (EQ_MP (@lem51255 _5146 _5153 _5154 t x y) (@lem51251 _5146 _5153 _5154 t x y)). Qed.
Lemma lem51257 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (x : _5154) (y : _5153) : (term46 _5146 _5153 _5154 t x y) = (term18 _5146 _5153 _5154 t x y).
Proof. exact (@lem51256 _5146 _5153 _5154 t x y). Qed.
Lemma lem51258 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (p1 : _5154) (p2 : _5153) : (term46 _5146 _5153 _5154 t p1 p2) = (term18 _5146 _5153 _5154 t p1 p2).
Proof. exact (@lem51257 _5146 _5153 _5154 t p1 p2). Qed.
Lemma lem51259 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (p1 : _5154) (p2 : _5153) : ((term47 _5146 _5153 _5154 t p1 p2) = (term46 _5146 _5153 _5154 t p1 p2)) = ((term18 _5146 _5153 _5154 t p1 p2) = (term18 _5146 _5153 _5154 t p1 p2)).
Proof. exact (MK_COMB (@lem51073 _5146 _5153 _5154 t p1 p2) (@lem51258 _5146 _5153 _5154 t p1 p2)). Qed.
Lemma lem51261 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem51262 {_5146 : Type'} (x : _5146) : (x = x) = True.
Proof. exact (@lem51261 _5146 x). Qed.
Lemma lem51263 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (p1 : _5154) (p2 : _5153) : ((term18 _5146 _5153 _5154 t p1 p2) = (term18 _5146 _5153 _5154 t p1 p2)) = True.
Proof. exact (@lem51262 _5146 (term18 _5146 _5153 _5154 t p1 p2)). Qed.
Lemma lem51264 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (p1 : _5154) (p2 : _5153) : ((term47 _5146 _5153 _5154 t p1 p2) = (term46 _5146 _5153 _5154 t p1 p2)) = True.
Proof. exact (TRANS (@lem51259 _5146 _5153 _5154 t p1 p2) (@lem51263 _5146 _5153 _5154 t p1 p2)). Qed.
Lemma lem51265 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (p1 : _5154) : (term48 _5146 _5153 _5154 t p1) = (term49 _5153).
Proof. exact (fun_ext (fun p2 : _5153 => @lem51264 _5146 _5153 _5154 t p1 p2)). Qed.
Lemma lem51266 {_5153 : Type'} : (@all _5153) = (@all _5153).
Proof. exact (eq_refl (@all _5153)). Qed.
Lemma lem51267 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (p1 : _5154) : (term50 _5146 _5153 _5154 t p1) = (term51 _5153).
Proof. exact (MK_COMB (@lem51266 _5153) (@lem51265 _5146 _5153 _5154 t p1)). Qed.
Lemma lem51269 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem51270 {_5153 : Type'} (t : Prop) : (term52 _5153 t) = t.
Proof. exact (@lem51269 _5153 t). Qed.
Lemma lem51271 {_5153 : Type'} : (term51 _5153) = True.
Proof. exact (@lem51270 _5153 True). Qed.
Lemma lem51272 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (p1 : _5154) : (term50 _5146 _5153 _5154 t p1) = True.
Proof. exact (TRANS (@lem51267 _5146 _5153 _5154 t p1) (@lem51271 _5153)). Qed.
Lemma lem51273 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) : (term53 _5146 _5153 _5154 t) = (term49 _5154).
Proof. exact (fun_ext (fun p1 : _5154 => @lem51272 _5146 _5153 _5154 t p1)). Qed.
Lemma lem51274 {_5154 : Type'} : (@all _5154) = (@all _5154).
Proof. exact (eq_refl (@all _5154)). Qed.
Lemma lem51275 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) : (term54 _5146 _5153 _5154 t) = (term51 _5154).
Proof. exact (MK_COMB (@lem51274 _5154) (@lem51273 _5146 _5153 _5154 t)). Qed.
Lemma lem51277 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem51278 {_5154 : Type'} (t : Prop) : (term52 _5154 t) = t.
Proof. exact (@lem51277 _5154 t). Qed.
Lemma lem51279 {_5154 : Type'} : (term51 _5154) = True.
Proof. exact (@lem51278 _5154 True). Qed.
Lemma lem51280 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) : (term54 _5146 _5153 _5154 t) = True.
Proof. exact (TRANS (@lem51275 _5146 _5153 _5154 t) (@lem51279 _5154)). Qed.
Lemma lem51281 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) : ((term55 _5146 _5153 _5154 t) = (term56 _5146 _5153 _5154 t)) = True.
Proof. exact (TRANS (@lem51057 _5146 _5153 _5154 t) (@lem51280 _5146 _5153 _5154 t)). Qed.
Lemma lem51282 {_5146 _5153 _5154 : Type'} : (term57 _5146 _5153 _5154) = (term58 _5146 _5153 _5154).
Proof. exact (fun_ext (fun t : type1228 _5146 _5153 _5154 => @lem51281 _5146 _5153 _5154 t)). Qed.
Lemma lem51283 {_5146 _5153 _5154 : Type'} : (@all ((prod _5154 _5153) -> _5146)) = (@all ((prod _5154 _5153) -> _5146)).
Proof. exact (eq_refl (@all ((prod _5154 _5153) -> _5146))). Qed.
Lemma lem51284 {_5146 _5153 _5154 : Type'} : (term59 _5146 _5153 _5154) = (term60 _5146 _5153 _5154).
Proof. exact (MK_COMB (@lem51283 _5146 _5153 _5154) (@lem51282 _5146 _5153 _5154)). Qed.
Lemma lem51286 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem51287 {_5146 _5153 _5154 : Type'} (t : Prop) : (term61 _5146 _5153 _5154 t) = t.
Proof. exact (@lem51286 (type1228 _5146 _5153 _5154) t). Qed.
Lemma lem51288 {_5146 _5153 _5154 : Type'} : (term60 _5146 _5153 _5154) = True.
Proof. exact (@lem51287 _5146 _5153 _5154 True). Qed.
Lemma lem51289 {_5146 _5153 _5154 : Type'} : (term59 _5146 _5153 _5154) = True.
Proof. exact (TRANS (@lem51284 _5146 _5153 _5154) (@lem51288 _5146 _5153 _5154)). Qed.
Lemma lem51290 {_5146 _5153 _5154 : Type'} : True = (term59 _5146 _5153 _5154).
Proof. exact (SYM (@lem51289 _5146 _5153 _5154)). Qed.
Lemma lem51291 {_5146 _5153 _5154 : Type'} : term59 _5146 _5153 _5154.
Proof. exact (EQ_MP (@lem51290 _5146 _5153 _5154) (@lem0)). Qed.
