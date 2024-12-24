Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1032609_term_abbrevs.
Require Import CONTRAPOS_THM_spec.
Require Import DE_MORGAN_THM_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm82_spec.
Lemma lem1032121 (t2 : Prop) (t1 : Prop) (h1 : (term0 t1 t2) = (t2 -> t1)) : (term0 t1 t2) = (t2 -> t1).
Proof. exact (h1). Qed.
Lemma lem1032122 (t2 : Prop) (t1 : Prop) (h1 : (term0 t1 t2) = (t2 -> t1)) : (t2 -> t1) = (term0 t1 t2).
Proof. exact (SYM (@lem1032121 t2 t1 h1)). Qed.
Lemma lem1032123 (t1 : Prop) (t2 : Prop) (h1 : (t2 -> t1) = (term0 t1 t2)) : (t2 -> t1) = (term0 t1 t2).
Proof. exact (h1). Qed.
Lemma lem1032124 (t1 : Prop) (t2 : Prop) (h1 : (t2 -> t1) = (term0 t1 t2)) : (term0 t1 t2) = (t2 -> t1).
Proof. exact (SYM (@lem1032123 t1 t2 h1)). Qed.
Lemma lem1032125 (t1 : Prop) (t2 : Prop) : ((term0 t1 t2) = (t2 -> t1)) = ((t2 -> t1) = (term0 t1 t2)).
Proof. exact (prop_ext (fun h1 : (term0 t1 t2) = (t2 -> t1) => @lem1032122 t2 t1 h1) (fun h1 : (t2 -> t1) = (term0 t1 t2) => @lem1032124 t1 t2 h1)). Qed.
Lemma lem1032126 (t1 : Prop) : (term1 t1) = (term2 t1).
Proof. exact (fun_ext (fun t2 : Prop => @lem1032125 t1 t2)). Qed.
Lemma lem1032127 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem1032128 (t1 : Prop) : (term3 t1) = (term4 t1).
Proof. exact (MK_COMB (@lem1032127) (@lem1032126 t1)). Qed.
Lemma lem1032129 : term5 = term6.
Proof. exact (fun_ext (fun t1 : Prop => @lem1032128 t1)). Qed.
Lemma lem1032130 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem1032131 : term7 = term8.
Proof. exact (MK_COMB (@lem1032130) (@lem1032129)). Qed.
Lemma lem1032132 : term8.
Proof. exact (EQ_MP (@lem1032131) (@lem10414)). Qed.
Lemma lem1032133 (t1 : Prop) : term9 t1.
Proof. exact (@lem1032132 t1). Qed.
Lemma lem1032134 (t1 : Prop) : (term9 t1) = (term4 t1).
Proof. exact (eq_refl (term9 t1)). Qed.
Lemma lem1032135 (t1 : Prop) : term4 t1.
Proof. exact (EQ_MP (@lem1032134 t1) (@lem1032133 t1)). Qed.
Lemma lem1032136 (t1 : Prop) (t2 : Prop) : term10 t1 t2.
Proof. exact (@lem1032135 t1 t2). Qed.
Lemma lem1032137 (t1 : Prop) (t2 : Prop) : (term10 t1 t2) = ((t2 -> t1) = (term0 t1 t2)).
Proof. exact (eq_refl (term10 t1 t2)). Qed.
Lemma lem1032142 (t1 : Prop) (t2 : Prop) (h1 : (term11 t1 t2) = (term12 t1 t2)) : (term11 t1 t2) = (term12 t1 t2).
Proof. exact (h1). Qed.
Lemma lem1032143 (t1 : Prop) (t2 : Prop) (h1 : (term11 t1 t2) = (term12 t1 t2)) : (term12 t1 t2) = (term11 t1 t2).
Proof. exact (SYM (@lem1032142 t1 t2 h1)). Qed.
Lemma lem1032144 (t1 : Prop) (t2 : Prop) (h1 : (term12 t1 t2) = (term11 t1 t2)) : (term12 t1 t2) = (term11 t1 t2).
Proof. exact (h1). Qed.
Lemma lem1032145 (t1 : Prop) (t2 : Prop) (h1 : (term12 t1 t2) = (term11 t1 t2)) : (term11 t1 t2) = (term12 t1 t2).
Proof. exact (SYM (@lem1032144 t1 t2 h1)). Qed.
Lemma lem1032146 (t1 : Prop) (t2 : Prop) : ((term11 t1 t2) = (term12 t1 t2)) = ((term12 t1 t2) = (term11 t1 t2)).
Proof. exact (prop_ext (fun h1 : (term11 t1 t2) = (term12 t1 t2) => @lem1032143 t1 t2 h1) (fun h1 : (term12 t1 t2) = (term11 t1 t2) => @lem1032145 t1 t2 h1)). Qed.
Lemma lem1032147 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1032148 (t1 : Prop) (t2 : Prop) : (term13 t1 t2) = (term14 t1 t2).
Proof. exact (MK_COMB (@lem1032147) (@lem1032146 t1 t2)). Qed.
Lemma lem1032149 (t1 : Prop) (t2 : Prop) (h1 : (term15 t1 t2) = (term16 t1 t2)) : (term15 t1 t2) = (term16 t1 t2).
Proof. exact (h1). Qed.
Lemma lem1032150 (t1 : Prop) (t2 : Prop) (h1 : (term15 t1 t2) = (term16 t1 t2)) : (term16 t1 t2) = (term15 t1 t2).
Proof. exact (SYM (@lem1032149 t1 t2 h1)). Qed.
Lemma lem1032151 (t1 : Prop) (t2 : Prop) (h1 : (term16 t1 t2) = (term15 t1 t2)) : (term16 t1 t2) = (term15 t1 t2).
Proof. exact (h1). Qed.
Lemma lem1032152 (t1 : Prop) (t2 : Prop) (h1 : (term16 t1 t2) = (term15 t1 t2)) : (term15 t1 t2) = (term16 t1 t2).
Proof. exact (SYM (@lem1032151 t1 t2 h1)). Qed.
Lemma lem1032153 (t1 : Prop) (t2 : Prop) : ((term15 t1 t2) = (term16 t1 t2)) = ((term16 t1 t2) = (term15 t1 t2)).
Proof. exact (prop_ext (fun h1 : (term15 t1 t2) = (term16 t1 t2) => @lem1032150 t1 t2 h1) (fun h1 : (term16 t1 t2) = (term15 t1 t2) => @lem1032152 t1 t2 h1)). Qed.
Lemma lem1032154 (t1 : Prop) (t2 : Prop) : (term17 t1 t2) = (term18 t1 t2).
Proof. exact (MK_COMB (@lem1032148 t1 t2) (@lem1032153 t1 t2)). Qed.
Lemma lem1032155 (t1 : Prop) : (term19 t1) = (term20 t1).
Proof. exact (fun_ext (fun t2 : Prop => @lem1032154 t1 t2)). Qed.
Lemma lem1032156 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem1032157 (t1 : Prop) : (term21 t1) = (term22 t1).
Proof. exact (MK_COMB (@lem1032156) (@lem1032155 t1)). Qed.
Lemma lem1032158 : term23 = term24.
Proof. exact (fun_ext (fun t1 : Prop => @lem1032157 t1)). Qed.
Lemma lem1032159 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem1032160 : term25 = term26.
Proof. exact (MK_COMB (@lem1032159) (@lem1032158)). Qed.
Lemma lem1032161 : term26.
Proof. exact (EQ_MP (@lem1032160) (@lem10089)). Qed.
Lemma lem1032162 {A : Type'} (n0 : A) (add : type1400 A) (mul : type1400 A) (h1 : term27 A n0 add mul) : term27 A n0 add mul.
Proof. exact (h1). Qed.
Lemma lem1032163 {A : Type'} (add : type1400 A) (mul : type1400 A) (h1 : term28 A add mul) : term28 A add mul.
Proof. exact (h1). Qed.
Lemma lem1032164 {A : Type'} (mul : type1400 A) (n0 : A) (h1 : term29 A mul n0) : term29 A mul n0.
Proof. exact (h1). Qed.
Lemma lem1032165 {A : Type'} (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : term30 A add mul.
Proof. exact (h1). Qed.
Lemma lem1032166 {A : Type'} (add : type1400 A) (h1 : term31 A add) : term31 A add.
Proof. exact (h1). Qed.
Lemma lem1032167 (t1 : Prop) : term32 t1.
Proof. exact (@lem1032161 t1). Qed.
Lemma lem1032168 (t1 : Prop) : (term32 t1) = (term22 t1).
Proof. exact (eq_refl (term32 t1)). Qed.
Lemma lem1032169 (t1 : Prop) : term22 t1.
Proof. exact (EQ_MP (@lem1032168 t1) (@lem1032167 t1)). Qed.
Lemma lem1032170 (t1 : Prop) (t2 : Prop) : term33 t1 t2.
Proof. exact (@lem1032169 t1 t2). Qed.
Lemma lem1032171 (t1 : Prop) (t2 : Prop) : (term33 t1 t2) = (term18 t1 t2).
Proof. exact (eq_refl (term33 t1 t2)). Qed.
Lemma lem1032172 (t1 : Prop) (t2 : Prop) : term18 t1 t2.
Proof. exact (EQ_MP (@lem1032171 t1 t2) (@lem1032170 t1 t2)). Qed.
Lemma lem1032187 {A : Type'} (w : A) (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : term34 A add mul w.
Proof. exact (@lem1032165 A add mul h1 w). Qed.
Lemma lem1032188 {A : Type'} (add : type1400 A) (mul : type1400 A) (w : A) : (term34 A add mul w) = (term35 A add mul w).
Proof. exact (eq_refl (term34 A add mul w)). Qed.
Lemma lem1032189 {A : Type'} (w : A) (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : term35 A add mul w.
Proof. exact (EQ_MP (@lem1032188 A add mul w) (@lem1032187 A w add mul h1)). Qed.
Lemma lem1032190 {A : Type'} (w : A) (x : A) (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : term36 A add mul w x.
Proof. exact (@lem1032189 A w add mul h1 x). Qed.
Lemma lem1032191 {A : Type'} (add : type1400 A) (mul : type1400 A) (w : A) (x : A) : (term36 A add mul w x) = (term37 A add mul w x).
Proof. exact (eq_refl (term36 A add mul w x)). Qed.
Lemma lem1032192 {A : Type'} (w : A) (x : A) (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : term37 A add mul w x.
Proof. exact (EQ_MP (@lem1032191 A add mul w x) (@lem1032190 A w x add mul h1)). Qed.
Lemma lem1032193 {A : Type'} (w : A) (x : A) (y : A) (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : term38 A add mul w x y.
Proof. exact (@lem1032192 A w x add mul h1 y). Qed.
Lemma lem1032194 {A : Type'} (add : type1400 A) (mul : type1400 A) (w : A) (x : A) (y : A) : (term38 A add mul w x y) = (term39 A add mul w x y).
Proof. exact (eq_refl (term38 A add mul w x y)). Qed.
Lemma lem1032195 {A : Type'} (w : A) (x : A) (y : A) (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : term39 A add mul w x y.
Proof. exact (EQ_MP (@lem1032194 A add mul w x y) (@lem1032193 A w x y add mul h1)). Qed.
Lemma lem1032196 {A : Type'} (w : A) (x : A) (y : A) (z : A) (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : term40 A add mul w x y z.
Proof. exact (@lem1032195 A w x y add mul h1 z). Qed.
Lemma lem1032197 {A : Type'} (add : type1400 A) (mul : type1400 A) (w : A) (x : A) (y : A) (z : A) : (term40 A add mul w x y z) = (((term41 A add w y mul x z) = (term41 A add w z mul x y)) = (term42 A w x y z)).
Proof. exact (eq_refl (term40 A add mul w x y z)). Qed.
Lemma lem1032220 (t1 : Prop) (t2 : Prop) : (term16 t1 t2) = (term15 t1 t2).
Proof. exact (proj2 (@lem1032172 t1 t2)). Qed.
Lemma lem1032221 {A : Type'} (a : A) (b : A) (c : A) (d : A) : (term43 A a b c d) = (term44 A a b c d).
Proof. exact (@lem1032220 (a = b) (c = d)). Qed.
Lemma lem1032228 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1032229 {A : Type'} (a : A) (b : A) (c : A) (d : A) : (term45 A a b c d) = (term46 A a b c d).
Proof. exact (MK_COMB (@lem1032228) (@lem1032221 A a b c d)). Qed.
Lemma lem1032231 {A : Type'} (w : A) (x : A) (y : A) (z : A) (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : ((term41 A add w y mul x z) = (term41 A add w z mul x y)) = (term42 A w x y z).
Proof. exact (EQ_MP (@lem1032197 A add mul w x y z) (@lem1032196 A w x y z add mul h1)). Qed.
Lemma lem1032232 {A : Type'} (w : A) (x : A) (y : A) (z : A) (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : ((term41 A add w y mul x z) = (term41 A add w z mul x y)) = (term42 A w x y z).
Proof. exact (@lem1032231 A w x y z add mul h1). Qed.
Lemma lem1032233 {A : Type'} (a : A) (b : A) (c : A) (d : A) (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : ((term41 A add a c mul b d) = (term41 A add a d mul b c)) = (term42 A a b c d).
Proof. exact (@lem1032232 A a b c d add mul h1). Qed.
Lemma lem1032240 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1032241 {A : Type'} (a : A) (b : A) (c : A) (d : A) (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : (term47 A add a d mul b c) = (term44 A a b c d).
Proof. exact (MK_COMB (@lem1032240) (@lem1032233 A a b c d add mul h1)). Qed.
Lemma lem1032242 {A : Type'} (a : A) (b : A) (c : A) (d : A) (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : ((term43 A a b c d) = (term47 A add a d mul b c)) = ((term44 A a b c d) = (term44 A a b c d)).
Proof. exact (MK_COMB (@lem1032229 A a b c d) (@lem1032241 A a b c d add mul h1)). Qed.
Lemma lem1032244 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1032245 (x : Prop) : (x = x) = True.
Proof. exact (@lem1032244 Prop x). Qed.
Lemma lem1032246 {A : Type'} (a : A) (b : A) (c : A) (d : A) : ((term44 A a b c d) = (term44 A a b c d)) = True.
Proof. exact (@lem1032245 (term44 A a b c d)). Qed.
Lemma lem1032247 {A : Type'} (a : A) (d : A) (b : A) (c : A) (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : ((term43 A a b c d) = (term47 A add a d mul b c)) = True.
Proof. exact (TRANS (@lem1032242 A a b c d add mul h1) (@lem1032246 A a b c d)). Qed.
Lemma lem1032248 {A : Type'} (a : A) (b : A) (c : A) (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : (term48 A add a mul b c) = (term49 A).
Proof. exact (fun_ext (fun d : A => @lem1032247 A a d b c add mul h1)). Qed.
Lemma lem1032249 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1032250 {A : Type'} (a : A) (b : A) (c : A) (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : (term50 A add a mul b c) = (term51 A).
Proof. exact (MK_COMB (@lem1032249 A) (@lem1032248 A a b c add mul h1)). Qed.
Lemma lem1032252 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1032253 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (@lem1032252 A t). Qed.
Lemma lem1032254 {A : Type'} : (term51 A) = True.
Proof. exact (@lem1032253 A True). Qed.
Lemma lem1032255 {A : Type'} (a : A) (b : A) (c : A) (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : (term50 A add a mul b c) = True.
Proof. exact (TRANS (@lem1032250 A a b c add mul h1) (@lem1032254 A)). Qed.
Lemma lem1032256 {A : Type'} (a : A) (b : A) (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : (term53 A add a mul b) = (term49 A).
Proof. exact (fun_ext (fun c : A => @lem1032255 A a b c add mul h1)). Qed.
Lemma lem1032257 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1032258 {A : Type'} (a : A) (b : A) (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : (term54 A add a mul b) = (term51 A).
Proof. exact (MK_COMB (@lem1032257 A) (@lem1032256 A a b add mul h1)). Qed.
Lemma lem1032260 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1032261 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (@lem1032260 A t). Qed.
Lemma lem1032262 {A : Type'} : (term51 A) = True.
Proof. exact (@lem1032261 A True). Qed.
Lemma lem1032263 {A : Type'} (a : A) (b : A) (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : (term54 A add a mul b) = True.
Proof. exact (TRANS (@lem1032258 A a b add mul h1) (@lem1032262 A)). Qed.
Lemma lem1032264 {A : Type'} (a : A) (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : (term55 A add a mul) = (term49 A).
Proof. exact (fun_ext (fun b : A => @lem1032263 A a b add mul h1)). Qed.
Lemma lem1032265 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1032266 {A : Type'} (a : A) (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : (term56 A add a mul) = (term51 A).
Proof. exact (MK_COMB (@lem1032265 A) (@lem1032264 A a add mul h1)). Qed.
Lemma lem1032268 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1032269 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (@lem1032268 A t). Qed.
Lemma lem1032270 {A : Type'} : (term51 A) = True.
Proof. exact (@lem1032269 A True). Qed.
Lemma lem1032271 {A : Type'} (a : A) (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : (term56 A add a mul) = True.
Proof. exact (TRANS (@lem1032266 A a add mul h1) (@lem1032270 A)). Qed.
Lemma lem1032272 {A : Type'} (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : (term57 A add mul) = (term49 A).
Proof. exact (fun_ext (fun a : A => @lem1032271 A a add mul h1)). Qed.
Lemma lem1032273 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1032274 {A : Type'} (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : (term58 A add mul) = (term51 A).
Proof. exact (MK_COMB (@lem1032273 A) (@lem1032272 A add mul h1)). Qed.
Lemma lem1032276 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1032277 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (@lem1032276 A t). Qed.
Lemma lem1032278 {A : Type'} : (term51 A) = True.
Proof. exact (@lem1032277 A True). Qed.
Lemma lem1032279 {A : Type'} (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : (term58 A add mul) = True.
Proof. exact (TRANS (@lem1032274 A add mul h1) (@lem1032278 A)). Qed.
Lemma lem1032280 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1032281 {A : Type'} (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : (term59 A add mul) = (and True).
Proof. exact (MK_COMB (@lem1032280) (@lem1032279 A add mul h1)). Qed.
Lemma lem1032318 {A : Type'} (n0 : A) (add : type1400 A) (mul : type1400 A) : (term60 A n0 add mul) = (term60 A n0 add mul).
Proof. exact (eq_refl (term60 A n0 add mul)). Qed.
Lemma lem1032319 {A : Type'} (n0 : A) (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : (term61 A n0 add mul) = (term62 A n0 add mul).
Proof. exact (MK_COMB (@lem1032281 A add mul h1) (@lem1032318 A n0 add mul)). Qed.
Lemma lem1032321 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1032322 {A : Type'} (n0 : A) (add : type1400 A) (mul : type1400 A) : (term62 A n0 add mul) = (term60 A n0 add mul).
Proof. exact (@lem1032321 (term60 A n0 add mul)). Qed.
Lemma lem1032359 {A : Type'} (n0 : A) (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : (term61 A n0 add mul) = (term60 A n0 add mul).
Proof. exact (TRANS (@lem1032319 A n0 add mul h1) (@lem1032322 A n0 add mul)). Qed.
Lemma lem1032360 {A : Type'} (n0 : A) (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : (term60 A n0 add mul) = (term61 A n0 add mul).
Proof. exact (SYM (@lem1032359 A n0 add mul h1)). Qed.
Lemma lem1032361 {A : Type'} (n : A) (n0 : A) (h1 : term63 A n n0) : term63 A n n0.
Proof. exact (h1). Qed.
Lemma lem1032362 {A : Type'} (a : A) (b : A) (c : A) (d : A) (h1 : term64 A a b c d) : term64 A a b c d.
Proof. exact (h1). Qed.
Lemma lem1032363 {A : Type'} (c : A) (d : A) (h1 : term63 A c d) : term63 A c d.
Proof. exact (h1). Qed.
Lemma lem1032364 {A : Type'} (a : A) (b : A) (h1 : a = b) : a = b.
Proof. exact (h1). Qed.
Lemma lem1032365 {A : Type'} (n0 : A) (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : term34 A add mul n0.
Proof. exact (@lem1032165 A add mul h1 n0). Qed.
Lemma lem1032366 {A : Type'} (add : type1400 A) (mul : type1400 A) (n0 : A) : (term34 A add mul n0) = (term35 A add mul n0).
Proof. exact (eq_refl (term34 A add mul n0)). Qed.
Lemma lem1032367 {A : Type'} (n0 : A) (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : term35 A add mul n0.
Proof. exact (EQ_MP (@lem1032366 A add mul n0) (@lem1032365 A n0 add mul h1)). Qed.
Lemma lem1032368 {A : Type'} (n0 : A) (n : A) (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : term36 A add mul n0 n.
Proof. exact (@lem1032367 A n0 add mul h1 n). Qed.
Lemma lem1032369 {A : Type'} (add : type1400 A) (mul : type1400 A) (n0 : A) (n : A) : (term36 A add mul n0 n) = (term37 A add mul n0 n).
Proof. exact (eq_refl (term36 A add mul n0 n)). Qed.
Lemma lem1032370 {A : Type'} (n0 : A) (n : A) (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : term37 A add mul n0 n.
Proof. exact (EQ_MP (@lem1032369 A add mul n0 n) (@lem1032368 A n0 n add mul h1)). Qed.
Lemma lem1032371 {A : Type'} (n0 : A) (n : A) (d : A) (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : term38 A add mul n0 n d.
Proof. exact (@lem1032370 A n0 n add mul h1 d). Qed.
Lemma lem1032372 {A : Type'} (add : type1400 A) (mul : type1400 A) (n0 : A) (n : A) (d : A) : (term38 A add mul n0 n d) = (term39 A add mul n0 n d).
Proof. exact (eq_refl (term38 A add mul n0 n d)). Qed.
Lemma lem1032373 {A : Type'} (n0 : A) (n : A) (d : A) (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : term39 A add mul n0 n d.
Proof. exact (EQ_MP (@lem1032372 A add mul n0 n d) (@lem1032371 A n0 n d add mul h1)). Qed.
Lemma lem1032374 {A : Type'} (n0 : A) (n : A) (d : A) (c : A) (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : term40 A add mul n0 n d c.
Proof. exact (@lem1032373 A n0 n d add mul h1 c). Qed.
Lemma lem1032375 {A : Type'} (add : type1400 A) (mul : type1400 A) (n0 : A) (n : A) (d : A) (c : A) : (term40 A add mul n0 n d c) = (((term41 A add n0 d mul n c) = (term41 A add n0 c mul n d)) = (term42 A n0 n d c)).
Proof. exact (eq_refl (term40 A add mul n0 n d c)). Qed.
Lemma lem1032376 {A : Type'} (n0 : A) (n : A) (d : A) (c : A) (add : type1400 A) (mul : type1400 A) (h1 : term30 A add mul) : ((term41 A add n0 d mul n c) = (term41 A add n0 c mul n d)) = (term42 A n0 n d c).
Proof. exact (EQ_MP (@lem1032375 A add mul n0 n d c) (@lem1032374 A n0 n d c add mul h1)). Qed.
Lemma lem1032382 (t1 : Prop) (t2 : Prop) : (t2 -> t1) = (term0 t1 t2).
Proof. exact (EQ_MP (@lem1032137 t1 t2) (@lem1032136 t1 t2)). Qed.
Lemma lem1032383 {A : Type'} (a : A) (b : A) (add : type1400 A) (mul : type1400 A) (n0 : A) (n : A) (d : A) (c : A) : (term65 A n0 a c add b mul n d) = (term66 A a b add mul n0 n d c).
Proof. exact (@lem1032382 (term67 A a c add b mul n d) (((term41 A add n0 d mul n c) = (term41 A add n0 c mul n d)) = (term42 A n0 n d c))). Qed.
Lemma lem1032384 {A : Type'} (n0 : A) (a : A) (c : A) (add : type1400 A) (b : A) (mul : type1400 A) (n : A) (d : A) : (term66 A a b add mul n0 n d c) = (term65 A n0 a c add b mul n d).
Proof. exact (SYM (@lem1032383 A a b add mul n0 n d c)). Qed.
Lemma lem1032385 {A : Type'} (x : A) (mul : type1400 A) (n0 : A) (h1 : term29 A mul n0) : term68 A mul n0 x.
Proof. exact (@lem1032164 A mul n0 h1 x). Qed.
Lemma lem1032386 {A : Type'} (mul : type1400 A) (x : A) (n0 : A) : (term68 A mul n0 x) = ((mul n0 x) = n0).
Proof. exact (eq_refl (term68 A mul n0 x)). Qed.
Lemma lem1032388 {A : Type'} (x : A) (add : type1400 A) (h1 : term31 A add) : term69 A add x.
Proof. exact (@lem1032166 A add h1 x). Qed.
Lemma lem1032389 {A : Type'} (add : type1400 A) (x : A) : (term69 A add x) = (term70 A add x).
Proof. exact (eq_refl (term69 A add x)). Qed.
Lemma lem1032390 {A : Type'} (x : A) (add : type1400 A) (h1 : term31 A add) : term70 A add x.
Proof. exact (EQ_MP (@lem1032389 A add x) (@lem1032388 A x add h1)). Qed.
Lemma lem1032391 {A : Type'} (x : A) (y : A) (add : type1400 A) (h1 : term31 A add) : term71 A add x y.
Proof. exact (@lem1032390 A x add h1 y). Qed.
Lemma lem1032392 {A : Type'} (add : type1400 A) (x : A) (y : A) : (term71 A add x y) = (term72 A add x y).
Proof. exact (eq_refl (term71 A add x y)). Qed.
Lemma lem1032393 {A : Type'} (x : A) (y : A) (add : type1400 A) (h1 : term31 A add) : term72 A add x y.
Proof. exact (EQ_MP (@lem1032392 A add x y) (@lem1032391 A x y add h1)). Qed.
Lemma lem1032394 {A : Type'} (x : A) (y : A) (z : A) (add : type1400 A) (h1 : term31 A add) : term73 A add x y z.
Proof. exact (@lem1032393 A x y add h1 z). Qed.
Lemma lem1032395 {A : Type'} (add : type1400 A) (x : A) (y : A) (z : A) : (term73 A add x y z) = (((add x y) = (add x z)) = (y = z)).
Proof. exact (eq_refl (term73 A add x y z)). Qed.
Lemma lem1032400 {A : Type'} (n : A) (n0 : A) (h1 : n = n0) : n = n0.
Proof. exact (h1). Qed.
Lemma lem1032401 {A : Type'} (n : A) (n0 : A) (h1 : n = n0) : n0 = n.
Proof. exact (SYM (@lem1032400 A n n0 h1)). Qed.
Lemma lem1032402 {A : Type'} (n0 : A) (n : A) (h1 : n0 = n) : n0 = n.
Proof. exact (h1). Qed.
Lemma lem1032403 {A : Type'} (n0 : A) (n : A) (h1 : n0 = n) : n = n0.
Proof. exact (SYM (@lem1032402 A n0 n h1)). Qed.
Lemma lem1032404 {A : Type'} (n0 : A) (n : A) : (n = n0) = (n0 = n).
Proof. exact (prop_ext (fun h1 : n = n0 => @lem1032401 A n n0 h1) (fun h1 : n0 = n => @lem1032403 A n0 n h1)). Qed.
Lemma lem1032405 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1032406 {A : Type'} (n0 : A) (n : A) : (term63 A n n0) = (term63 A n0 n).
Proof. exact (MK_COMB (@lem1032405) (@lem1032404 A n0 n)). Qed.
Lemma lem1032407 {A : Type'} (n : A) (n0 : A) (h1 : term63 A n n0) : term63 A n0 n.
Proof. exact (EQ_MP (@lem1032406 A n0 n) (@lem1032361 A n n0 h1)). Qed.
Lemma lem1032408 {A : Type'} (n0 : A) (n : A) : term74 A n0 n.
Proof. exact (@lem82 (n0 = n)). Qed.
Lemma lem1032413 {A : Type'} (c : A) (d : A) (h1 : c = d) : c = d.
Proof. exact (h1). Qed.
Lemma lem1032414 {A : Type'} (c : A) (d : A) (h1 : c = d) : d = c.
Proof. exact (SYM (@lem1032413 A c d h1)). Qed.
Lemma lem1032415 {A : Type'} (d : A) (c : A) (h1 : d = c) : d = c.
Proof. exact (h1). Qed.
Lemma lem1032416 {A : Type'} (d : A) (c : A) (h1 : d = c) : c = d.
Proof. exact (SYM (@lem1032415 A d c h1)). Qed.
Lemma lem1032417 {A : Type'} (d : A) (c : A) : (c = d) = (d = c).
Proof. exact (prop_ext (fun h1 : c = d => @lem1032414 A c d h1) (fun h1 : d = c => @lem1032416 A d c h1)). Qed.
Lemma lem1032418 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1032419 {A : Type'} (d : A) (c : A) : (term63 A c d) = (term63 A d c).
Proof. exact (MK_COMB (@lem1032418) (@lem1032417 A d c)). Qed.
Lemma lem1032420 {A : Type'} (c : A) (d : A) (h1 : term63 A c d) : term63 A d c.
Proof. exact (EQ_MP (@lem1032419 A d c) (@lem1032363 A c d h1)). Qed.
Lemma lem1032421 {A : Type'} (d : A) (c : A) : term74 A d c.
Proof. exact (@lem82 (d = c)). Qed.
Lemma lem1032426 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term75 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1032427 (p : Prop) (q : Prop) (p' : Prop) : term76 p q p'.
Proof. exact (fun q' : Prop => @lem1032426 p q p' q'). Qed.
Lemma lem1032428 (p : Prop) (q : Prop) : term77 p q.
Proof. exact (fun p' : Prop => @lem1032427 p q p'). Qed.
Lemma lem1032429 {A : Type'} (a : A) (b : A) (add : type1400 A) (mul : type1400 A) (n0 : A) (n : A) (d : A) (c : A) : term78 A a b add mul n0 n d c.
Proof. exact (@lem1032428 (term79 A a c add b mul n d) (term80 A add mul n0 n d c)). Qed.
Lemma lem1032430 {A : Type'} (a : A) (b : A) (add : type1400 A) (mul : type1400 A) (n0 : A) (n : A) (d : A) (c : A) (p' : Prop) : term81 A a b add mul n0 n d c p'.
Proof. exact (@lem1032429 A a b add mul n0 n d c p'). Qed.
Lemma lem1032431 {A : Type'} (a : A) (b : A) (add : type1400 A) (mul : type1400 A) (n0 : A) (n : A) (d : A) (c : A) (p' : Prop) : (term81 A a b add mul n0 n d c p') = (term82 A a b add mul n0 n d c p').
Proof. exact (eq_refl (term81 A a b add mul n0 n d c p')). Qed.
Lemma lem1032432 {A : Type'} (a : A) (b : A) (add : type1400 A) (mul : type1400 A) (n0 : A) (n : A) (d : A) (c : A) (p' : Prop) : term82 A a b add mul n0 n d c p'.
Proof. exact (EQ_MP (@lem1032431 A a b add mul n0 n d c p') (@lem1032430 A a b add mul n0 n d c p')). Qed.
Lemma lem1032433 {A : Type'} (a : A) (b : A) (add : type1400 A) (mul : type1400 A) (n0 : A) (n : A) (d : A) (c : A) (p' : Prop) (q' : Prop) : term83 A a b add mul n0 n d c p' q'.
Proof. exact (@lem1032432 A a b add mul n0 n d c p' q'). Qed.
Lemma lem1032434 {A : Type'} (a : A) (b : A) (add : type1400 A) (mul : type1400 A) (n0 : A) (n : A) (d : A) (c : A) (p' : Prop) (q' : Prop) : (term83 A a b add mul n0 n d c p' q') = (term84 A a b add mul n0 n d c p' q').
Proof. exact (eq_refl (term83 A a b add mul n0 n d c p' q')). Qed.
Lemma lem1032435 {A : Type'} (a : A) (b : A) (add : type1400 A) (mul : type1400 A) (n0 : A) (n : A) (d : A) (c : A) (p' : Prop) (q' : Prop) : term84 A a b add mul n0 n d c p' q'.
Proof. exact (EQ_MP (@lem1032434 A a b add mul n0 n d c p' q') (@lem1032433 A a b add mul n0 n d c p' q')). Qed.
Lemma lem1032437 (t : Prop) : (term85 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem1032438 {A : Type'} (a : A) (c : A) (add : type1400 A) (b : A) (mul : type1400 A) (n : A) (d : A) : (term79 A a c add b mul n d) = ((term86 A add a mul n c) = (term86 A add b mul n d)).
Proof. exact (@lem1032437 ((term86 A add a mul n c) = (term86 A add b mul n d))). Qed.
Lemma lem1032444 {A : Type'} (a : A) (b : A) (h1 : a = b) : a = b.
Proof. exact (h1). Qed.
Lemma lem1032445 {A : Type'} (add : type1400 A) : add = add.
Proof. exact (eq_refl add). Qed.
Lemma lem1032446 {A : Type'} (add : type1400 A) (a : A) (b : A) (h1 : a = b) : (add a) = (add b).
Proof. exact (MK_COMB (@lem1032445 A add) (@lem1032444 A a b h1)). Qed.
Lemma lem1032447 {A : Type'} (mul : type1400 A) (n : A) (c : A) : (mul n c) = (mul n c).
Proof. exact (eq_refl (mul n c)). Qed.
Lemma lem1032448 {A : Type'} (add : type1400 A) (mul : type1400 A) (n : A) (c : A) (a : A) (b : A) (h1 : a = b) : (term86 A add a mul n c) = (term86 A add b mul n c).
Proof. exact (MK_COMB (@lem1032446 A add a b h1) (@lem1032447 A mul n c)). Qed.
Lemma lem1032449 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1032450 {A : Type'} (add : type1400 A) (mul : type1400 A) (n : A) (c : A) (a : A) (b : A) (h1 : a = b) : (term87 A add a mul n c) = (term87 A add b mul n c).
Proof. exact (MK_COMB (@lem1032449 A) (@lem1032448 A add mul n c a b h1)). Qed.
Lemma lem1032451 {A : Type'} (add : type1400 A) (b : A) (mul : type1400 A) (n : A) (d : A) : (term86 A add b mul n d) = (term86 A add b mul n d).
Proof. exact (eq_refl (term86 A add b mul n d)). Qed.
Lemma lem1032452 {A : Type'} (c : A) (add : type1400 A) (mul : type1400 A) (n : A) (d : A) (a : A) (b : A) (h1 : a = b) : ((term86 A add a mul n c) = (term86 A add b mul n d)) = ((term86 A add b mul n c) = (term86 A add b mul n d)).
Proof. exact (MK_COMB (@lem1032450 A add mul n c a b h1) (@lem1032451 A add b mul n d)). Qed.
Lemma lem1032454 {A : Type'} (x : A) (y : A) (z : A) (add : type1400 A) (h1 : term31 A add) : ((add x y) = (add x z)) = (y = z).
Proof. exact (EQ_MP (@lem1032395 A add x y z) (@lem1032394 A x y z add h1)). Qed.
Lemma lem1032455 {A : Type'} (x : A) (y : A) (z : A) (add : type1400 A) (h1 : term31 A add) : ((add x y) = (add x z)) = (y = z).
Proof. exact (@lem1032454 A x y z add h1). Qed.
Lemma lem1032456 {A : Type'} (b : A) (c : A) (mul : type1400 A) (n : A) (d : A) (add : type1400 A) (h1 : term31 A add) : ((term86 A add b mul n c) = (term86 A add b mul n d)) = ((mul n c) = (mul n d)).
Proof. exact (@lem1032455 A b (mul n c) (mul n d) add h1). Qed.
Lemma lem1032459 {A : Type'} (c : A) (mul : type1400 A) (n : A) (d : A) (add : type1400 A) (a : A) (b : A) (h1 : term31 A add) (h2 : a = b) : ((term86 A add a mul n c) = (term86 A add b mul n d)) = ((mul n c) = (mul n d)).
Proof. exact (TRANS (@lem1032452 A c add mul n d a b h2) (@lem1032456 A b c mul n d add h1)). Qed.
Lemma lem1032460 {A : Type'} (c : A) (mul : type1400 A) (n : A) (d : A) (add : type1400 A) (a : A) (b : A) (h1 : term31 A add) (h2 : a = b) : (term79 A a c add b mul n d) = ((mul n c) = (mul n d)).
Proof. exact (TRANS (@lem1032438 A a c add b mul n d) (@lem1032459 A c mul n d add a b h1 h2)). Qed.
Lemma lem1032461 {A : Type'} (a : A) (b : A) (add : type1400 A) (n0 : A) (c : A) (mul : type1400 A) (n : A) (d : A) (q' : Prop) : term88 A a b add n0 c mul n d q'.
Proof. exact (@lem1032435 A a b add mul n0 n d c ((mul n c) = (mul n d)) q'). Qed.
Lemma lem1032462 {A : Type'} (n0 : A) (c : A) (mul : type1400 A) (n : A) (d : A) (q' : Prop) (add : type1400 A) (a : A) (b : A) (h1 : term31 A add) (h2 : a = b) : term89 A a b add n0 c mul n d q'.
Proof. exact (@lem1032461 A a b add n0 c mul n d q' (@lem1032460 A c mul n d add a b h1 h2)). Qed.
Lemma lem1032471 {A : Type'} (x : A) (mul : type1400 A) (n0 : A) (h1 : term29 A mul n0) : (mul n0 x) = n0.
Proof. exact (EQ_MP (@lem1032386 A mul x n0) (@lem1032385 A x mul n0 h1)). Qed.
Lemma lem1032472 {A : Type'} (x : A) (mul : type1400 A) (n0 : A) (h1 : term29 A mul n0) : (mul n0 x) = n0.
Proof. exact (@lem1032471 A x mul n0 h1). Qed.
Lemma lem1032473 {A : Type'} (d : A) (mul : type1400 A) (n0 : A) (h1 : term29 A mul n0) : (mul n0 d) = n0.
Proof. exact (@lem1032472 A d mul n0 h1). Qed.
Lemma lem1032474 {A : Type'} (add : type1400 A) : add = add.
Proof. exact (eq_refl add). Qed.
Lemma lem1032475 {A : Type'} (d : A) (add : type1400 A) (mul : type1400 A) (n0 : A) (h1 : term29 A mul n0) : (term90 A add mul n0 d) = (add n0).
Proof. exact (MK_COMB (@lem1032474 A add) (@lem1032473 A d mul n0 h1)). Qed.
Lemma lem1032477 {A : Type'} (c : A) (mul : type1400 A) (n : A) (d : A) (h1 : (mul n c) = (mul n d)) : (mul n c) = (mul n d).
Proof. exact (h1). Qed.
Lemma lem1032478 {A : Type'} (add : type1400 A) (n0 : A) (c : A) (mul : type1400 A) (n : A) (d : A) (h1 : term29 A mul n0) (h2 : (mul n c) = (mul n d)) : (term41 A add n0 d mul n c) = (term86 A add n0 mul n d).
Proof. exact (MK_COMB (@lem1032475 A d add mul n0 h1) (@lem1032477 A c mul n d h2)). Qed.
Lemma lem1032479 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1032480 {A : Type'} (add : type1400 A) (n0 : A) (c : A) (mul : type1400 A) (n : A) (d : A) (h1 : term29 A mul n0) (h2 : (mul n c) = (mul n d)) : (term91 A add n0 d mul n c) = (term87 A add n0 mul n d).
Proof. exact (MK_COMB (@lem1032479 A) (@lem1032478 A add n0 c mul n d h1 h2)). Qed.
Lemma lem1032482 {A : Type'} (x : A) (mul : type1400 A) (n0 : A) (h1 : term29 A mul n0) : (mul n0 x) = n0.
Proof. exact (EQ_MP (@lem1032386 A mul x n0) (@lem1032385 A x mul n0 h1)). Qed.
Lemma lem1032483 {A : Type'} (x : A) (mul : type1400 A) (n0 : A) (h1 : term29 A mul n0) : (mul n0 x) = n0.
Proof. exact (@lem1032482 A x mul n0 h1). Qed.
Lemma lem1032484 {A : Type'} (c : A) (mul : type1400 A) (n0 : A) (h1 : term29 A mul n0) : (mul n0 c) = n0.
Proof. exact (@lem1032483 A c mul n0 h1). Qed.
Lemma lem1032485 {A : Type'} (add : type1400 A) : add = add.
Proof. exact (eq_refl add). Qed.
Lemma lem1032486 {A : Type'} (c : A) (add : type1400 A) (mul : type1400 A) (n0 : A) (h1 : term29 A mul n0) : (term90 A add mul n0 c) = (add n0).
Proof. exact (MK_COMB (@lem1032485 A add) (@lem1032484 A c mul n0 h1)). Qed.
Lemma lem1032487 {A : Type'} (mul : type1400 A) (n : A) (d : A) : (mul n d) = (mul n d).
Proof. exact (eq_refl (mul n d)). Qed.
Lemma lem1032488 {A : Type'} (c : A) (add : type1400 A) (n : A) (d : A) (mul : type1400 A) (n0 : A) (h1 : term29 A mul n0) : (term41 A add n0 c mul n d) = (term86 A add n0 mul n d).
Proof. exact (MK_COMB (@lem1032486 A c add mul n0 h1) (@lem1032487 A mul n d)). Qed.
Lemma lem1032489 {A : Type'} (add : type1400 A) (n0 : A) (c : A) (mul : type1400 A) (n : A) (d : A) (h1 : term29 A mul n0) (h2 : (mul n c) = (mul n d)) : ((term41 A add n0 d mul n c) = (term41 A add n0 c mul n d)) = ((term86 A add n0 mul n d) = (term86 A add n0 mul n d)).
Proof. exact (MK_COMB (@lem1032480 A add n0 c mul n d h1 h2) (@lem1032488 A c add n d mul n0 h1)). Qed.
Lemma lem1032491 {A : Type'} (x : A) (y : A) (z : A) (add : type1400 A) (h1 : term31 A add) : ((add x y) = (add x z)) = (y = z).
Proof. exact (EQ_MP (@lem1032395 A add x y z) (@lem1032394 A x y z add h1)). Qed.
Lemma lem1032492 {A : Type'} (x : A) (y : A) (z : A) (add : type1400 A) (h1 : term31 A add) : ((add x y) = (add x z)) = (y = z).
Proof. exact (@lem1032491 A x y z add h1). Qed.
Lemma lem1032493 {A : Type'} (n0 : A) (mul : type1400 A) (n : A) (d : A) (add : type1400 A) (h1 : term31 A add) : ((term86 A add n0 mul n d) = (term86 A add n0 mul n d)) = ((mul n d) = (mul n d)).
Proof. exact (@lem1032492 A n0 (mul n d) (mul n d) add h1). Qed.
Lemma lem1032495 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1032496 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1032495 A x). Qed.
Lemma lem1032497 {A : Type'} (mul : type1400 A) (n : A) (d : A) : ((mul n d) = (mul n d)) = True.
Proof. exact (@lem1032496 A (mul n d)). Qed.
Lemma lem1032498 {A : Type'} (n0 : A) (mul : type1400 A) (n : A) (d : A) (add : type1400 A) (h1 : term31 A add) : ((term86 A add n0 mul n d) = (term86 A add n0 mul n d)) = True.
Proof. exact (TRANS (@lem1032493 A n0 mul n d add h1) (@lem1032497 A mul n d)). Qed.
Lemma lem1032499 {A : Type'} (add : type1400 A) (n0 : A) (c : A) (mul : type1400 A) (n : A) (d : A) (h1 : term31 A add) (h2 : term29 A mul n0) (h3 : (mul n c) = (mul n d)) : ((term41 A add n0 d mul n c) = (term41 A add n0 c mul n d)) = True.
Proof. exact (TRANS (@lem1032489 A add n0 c mul n d h2 h3) (@lem1032498 A n0 mul n d add h1)). Qed.
Lemma lem1032500 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1032501 {A : Type'} (add : type1400 A) (n0 : A) (c : A) (mul : type1400 A) (n : A) (d : A) (h1 : term31 A add) (h2 : term29 A mul n0) (h3 : (mul n c) = (mul n d)) : (term92 A add n0 c mul n d) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1032500) (@lem1032499 A add n0 c mul n d h1 h2 h3)). Qed.
Lemma lem1032505 {A : Type'} (n : A) (n0 : A) (h1 : term63 A n n0) : (n0 = n) = False.
Proof. exact (@lem1032408 A n0 n (@lem1032407 A n n0 h1)). Qed.
Lemma lem1032506 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1032507 {A : Type'} (n : A) (n0 : A) (h1 : term63 A n n0) : (term93 A n0 n) = (or False).
Proof. exact (MK_COMB (@lem1032506) (@lem1032505 A n n0 h1)). Qed.
Lemma lem1032509 {A : Type'} (c : A) (d : A) (h1 : term63 A c d) : (d = c) = False.
Proof. exact (@lem1032421 A d c (@lem1032420 A c d h1)). Qed.
Lemma lem1032510 {A : Type'} (c : A) (d : A) (n : A) (n0 : A) (h1 : term63 A c d) (h2 : term63 A n n0) : (term42 A n0 n d c) = (False \/ False).
Proof. exact (MK_COMB (@lem1032507 A n n0 h2) (@lem1032509 A c d h1)). Qed.
Lemma lem1032512 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1032513 : (False \/ False) = False.
Proof. exact (@lem1032512 False). Qed.
Lemma lem1032514 {A : Type'} (c : A) (d : A) (n : A) (n0 : A) (h1 : term63 A c d) (h2 : term63 A n n0) : (term42 A n0 n d c) = False.
Proof. exact (TRANS (@lem1032510 A c d n n0 h1 h2) (@lem1032513)). Qed.
Lemma lem1032515 {A : Type'} (add : type1400 A) (n0 : A) (c : A) (mul : type1400 A) (n : A) (d : A) (h1 : term31 A add) (h2 : term29 A mul n0) (h3 : term63 A c d) (h4 : term63 A n n0) (h5 : (mul n c) = (mul n d)) : (((term41 A add n0 d mul n c) = (term41 A add n0 c mul n d)) = (term42 A n0 n d c)) = (True = False).
Proof. exact (MK_COMB (@lem1032501 A add n0 c mul n d h1 h2 h5) (@lem1032514 A c d n n0 h3 h4)). Qed.
Lemma lem1032517 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1032518 : (True = False) = False.
Proof. exact (@lem1032517 False). Qed.
Lemma lem1032519 {A : Type'} (add : type1400 A) (n0 : A) (c : A) (mul : type1400 A) (n : A) (d : A) (h1 : term31 A add) (h2 : term29 A mul n0) (h3 : term63 A c d) (h4 : term63 A n n0) (h5 : (mul n c) = (mul n d)) : (((term41 A add n0 d mul n c) = (term41 A add n0 c mul n d)) = (term42 A n0 n d c)) = False.
Proof. exact (TRANS (@lem1032515 A add n0 c mul n d h1 h2 h3 h4 h5) (@lem1032518)). Qed.
Lemma lem1032520 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1032521 {A : Type'} (add : type1400 A) (n0 : A) (c : A) (mul : type1400 A) (n : A) (d : A) (h1 : term31 A add) (h2 : term29 A mul n0) (h3 : term63 A c d) (h4 : term63 A n n0) (h5 : (mul n c) = (mul n d)) : (term80 A add mul n0 n d c) = (~ False).
Proof. exact (MK_COMB (@lem1032520) (@lem1032519 A add n0 c mul n d h1 h2 h3 h4 h5)). Qed.
Lemma lem1032523 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1032524 {A : Type'} (add : type1400 A) (n0 : A) (c : A) (mul : type1400 A) (n : A) (d : A) (h1 : term31 A add) (h2 : term29 A mul n0) (h3 : term63 A c d) (h4 : term63 A n n0) (h5 : (mul n c) = (mul n d)) : (term80 A add mul n0 n d c) = True.
Proof. exact (TRANS (@lem1032521 A add n0 c mul n d h1 h2 h3 h4 h5) (@lem1032523)). Qed.
Lemma lem1032525 {A : Type'} (add : type1400 A) (mul : type1400 A) (c : A) (d : A) (n : A) (n0 : A) (h1 : term31 A add) (h2 : term29 A mul n0) (h3 : term63 A c d) (h4 : term63 A n n0) : term94 A add mul n0 n d c.
Proof. exact (fun h0 : (mul n c) = (mul n d) => @lem1032524 A add n0 c mul n d h1 h2 h3 h4 h0). Qed.
Lemma lem1032526 {A : Type'} (n0 : A) (c : A) (mul : type1400 A) (n : A) (d : A) (add : type1400 A) (a : A) (b : A) (h1 : term31 A add) (h2 : a = b) : term95 A a b add n0 c mul n d.
Proof. exact (@lem1032462 A n0 c mul n d True add a b h1 h2). Qed.
Lemma lem1032527 {A : Type'} (add : type1400 A) (mul : type1400 A) (c : A) (d : A) (n : A) (n0 : A) (a : A) (b : A) (h1 : term31 A add) (h2 : term29 A mul n0) (h3 : term63 A c d) (h4 : term63 A n n0) (h5 : a = b) : (term66 A a b add mul n0 n d c) = (term96 A c mul n d).
Proof. exact (@lem1032526 A n0 c mul n d add a b h1 h5 (@lem1032525 A add mul c d n n0 h1 h2 h3 h4)). Qed.
Lemma lem1032531 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1032532 {A : Type'} (c : A) (mul : type1400 A) (n : A) (d : A) : (term96 A c mul n d) = True.
Proof. exact (@lem1032531 ((mul n c) = (mul n d))). Qed.
Lemma lem1032533 {A : Type'} (add : type1400 A) (mul : type1400 A) (c : A) (d : A) (n : A) (n0 : A) (a : A) (b : A) (h1 : term31 A add) (h2 : term29 A mul n0) (h3 : term63 A c d) (h4 : term63 A n n0) (h5 : a = b) : (term66 A a b add mul n0 n d c) = True.
Proof. exact (TRANS (@lem1032527 A add mul c d n n0 a b h1 h2 h3 h4 h5) (@lem1032532 A c mul n d)). Qed.
Lemma lem1032534 {A : Type'} (add : type1400 A) (mul : type1400 A) (c : A) (d : A) (n : A) (n0 : A) (a : A) (b : A) (h1 : term31 A add) (h2 : term29 A mul n0) (h3 : term63 A c d) (h4 : term63 A n n0) (h5 : a = b) : True = (term66 A a b add mul n0 n d c).
Proof. exact (SYM (@lem1032533 A add mul c d n n0 a b h1 h2 h3 h4 h5)). Qed.
Lemma lem1032535 {A : Type'} (add : type1400 A) (mul : type1400 A) (c : A) (d : A) (n : A) (n0 : A) (a : A) (b : A) (h1 : term31 A add) (h2 : term29 A mul n0) (h3 : term63 A c d) (h4 : term63 A n n0) (h5 : a = b) : term66 A a b add mul n0 n d c.
Proof. exact (EQ_MP (@lem1032534 A add mul c d n n0 a b h1 h2 h3 h4 h5) (@lem0)). Qed.
Lemma lem1032536 {A : Type'} (add : type1400 A) (mul : type1400 A) (c : A) (d : A) (n : A) (n0 : A) (a : A) (b : A) (h1 : term31 A add) (h2 : term29 A mul n0) (h3 : term63 A c d) (h4 : term63 A n n0) (h5 : a = b) : term65 A n0 a c add b mul n d.
Proof. exact (EQ_MP (@lem1032384 A n0 a c add b mul n d) (@lem1032535 A add mul c d n n0 a b h1 h2 h3 h4 h5)). Qed.
Lemma lem1032537 {A : Type'} (add : type1400 A) (mul : type1400 A) (c : A) (d : A) (n : A) (n0 : A) (a : A) (b : A) (h1 : term30 A add mul) (h2 : term31 A add) (h3 : term29 A mul n0) (h4 : term63 A c d) (h5 : term63 A n n0) (h6 : a = b) : term67 A a c add b mul n d.
Proof. exact (@lem1032536 A add mul c d n n0 a b h2 h3 h4 h5 h6 (@lem1032376 A n0 n d c add mul h1)). Qed.
Lemma lem1032538 {A : Type'} (a : A) (b : A) (c : A) (d : A) (h1 : term64 A a b c d) : term63 A c d.
Proof. exact (proj2 (@lem1032362 A a b c d h1)). Qed.
Lemma lem1032539 {A : Type'} (a : A) (b : A) (c : A) (d : A) (h1 : term64 A a b c d) : a = b.
Proof. exact (proj1 (@lem1032362 A a b c d h1)). Qed.
Lemma lem1032540 {A : Type'} (add : type1400 A) (mul : type1400 A) (c : A) (d : A) (n : A) (n0 : A) (a : A) (b : A) (h1 : term30 A add mul) (h2 : term31 A add) (h3 : term29 A mul n0) (h4 : term63 A c d) (h5 : term63 A n n0) (h6 : a = b) : (term63 A c d) = (term67 A a c add b mul n d).
Proof. exact (prop_ext (fun h7 : term63 A c d => @lem1032537 A add mul c d n n0 a b h1 h2 h3 h4 h5 h6) (fun h7 : term67 A a c add b mul n d => @lem1032363 A c d h4)). Qed.
Lemma lem1032541 {A : Type'} (add : type1400 A) (mul : type1400 A) (c : A) (d : A) (n : A) (n0 : A) (a : A) (b : A) (h1 : term30 A add mul) (h2 : term31 A add) (h3 : term29 A mul n0) (h4 : term63 A c d) (h5 : term63 A n n0) (h6 : a = b) : term67 A a c add b mul n d.
Proof. exact (EQ_MP (@lem1032540 A add mul c d n n0 a b h1 h2 h3 h4 h5 h6) (@lem1032363 A c d h4)). Qed.
Lemma lem1032542 {A : Type'} (add : type1400 A) (mul : type1400 A) (c : A) (d : A) (n : A) (n0 : A) (a : A) (b : A) (h1 : term30 A add mul) (h2 : term31 A add) (h3 : term29 A mul n0) (h4 : term63 A c d) (h5 : term63 A n n0) (h6 : a = b) : (a = b) = (term67 A a c add b mul n d).
Proof. exact (prop_ext (fun h7 : a = b => @lem1032541 A add mul c d n n0 a b h1 h2 h3 h4 h5 h6) (fun h7 : term67 A a c add b mul n d => @lem1032364 A a b h6)). Qed.
Lemma lem1032543 {A : Type'} (add : type1400 A) (mul : type1400 A) (c : A) (d : A) (n : A) (n0 : A) (a : A) (b : A) (h1 : term30 A add mul) (h2 : term31 A add) (h3 : term29 A mul n0) (h4 : term63 A c d) (h5 : term63 A n n0) (h6 : a = b) : term67 A a c add b mul n d.
Proof. exact (EQ_MP (@lem1032542 A add mul c d n n0 a b h1 h2 h3 h4 h5 h6) (@lem1032364 A a b h6)). Qed.
Lemma lem1032544 {A : Type'} (add : type1400 A) (mul : type1400 A) (n : A) (n0 : A) (c : A) (d : A) (a : A) (b : A) (h1 : term30 A add mul) (h2 : term31 A add) (h3 : term29 A mul n0) (h4 : term63 A n n0) (h5 : term64 A a b c d) (h6 : a = b) : (term63 A c d) = (term67 A a c add b mul n d).
Proof. exact (prop_ext (fun h7 : term63 A c d => @lem1032543 A add mul c d n n0 a b h1 h2 h3 h7 h4 h6) (fun h7 : term67 A a c add b mul n d => @lem1032538 A a b c d h5)). Qed.
Lemma lem1032545 {A : Type'} (add : type1400 A) (mul : type1400 A) (n : A) (n0 : A) (c : A) (d : A) (a : A) (b : A) (h1 : term30 A add mul) (h2 : term31 A add) (h3 : term29 A mul n0) (h4 : term63 A n n0) (h5 : term64 A a b c d) (h6 : a = b) : term67 A a c add b mul n d.
Proof. exact (EQ_MP (@lem1032544 A add mul n n0 c d a b h1 h2 h3 h4 h5 h6) (@lem1032538 A a b c d h5)). Qed.
Lemma lem1032546 {A : Type'} (add : type1400 A) (mul : type1400 A) (n : A) (n0 : A) (a : A) (b : A) (c : A) (d : A) (h1 : term30 A add mul) (h2 : term31 A add) (h3 : term29 A mul n0) (h4 : term63 A n n0) (h5 : term64 A a b c d) : (a = b) = (term67 A a c add b mul n d).
Proof. exact (prop_ext (fun h6 : a = b => @lem1032545 A add mul n n0 c d a b h1 h2 h3 h4 h5 h6) (fun h6 : term67 A a c add b mul n d => @lem1032539 A a b c d h5)). Qed.
Lemma lem1032547 {A : Type'} (add : type1400 A) (mul : type1400 A) (n : A) (n0 : A) (a : A) (b : A) (c : A) (d : A) (h1 : term30 A add mul) (h2 : term31 A add) (h3 : term29 A mul n0) (h4 : term63 A n n0) (h5 : term64 A a b c d) : term67 A a c add b mul n d.
Proof. exact (EQ_MP (@lem1032546 A add mul n n0 a b c d h1 h2 h3 h4 h5) (@lem1032539 A a b c d h5)). Qed.
Lemma lem1032548 {A : Type'} (a : A) (c : A) (b : A) (d : A) (add : type1400 A) (mul : type1400 A) (n : A) (n0 : A) (h1 : term30 A add mul) (h2 : term31 A add) (h3 : term29 A mul n0) (h4 : term63 A n n0) : term97 A a c add b mul n d.
Proof. exact (fun h0 : term64 A a b c d => @lem1032547 A add mul n n0 a b c d h1 h2 h3 h4 h0). Qed.
Lemma lem1032549 {A : Type'} (a : A) (c : A) (b : A) (n : A) (d : A) (add : type1400 A) (mul : type1400 A) (n0 : A) (h1 : term30 A add mul) (h2 : term31 A add) (h3 : term29 A mul n0) : term98 A n0 a c add b mul n d.
Proof. exact (fun h0 : term63 A n n0 => @lem1032548 A a c b d add mul n n0 h1 h2 h3 h0). Qed.
Lemma lem1032554 {A : Type'} (a : A) (c : A) (b : A) (n : A) (add : type1400 A) (mul : type1400 A) (n0 : A) (h1 : term30 A add mul) (h2 : term31 A add) (h3 : term29 A mul n0) : term99 A n0 a c add b mul n.
Proof. exact (fun d : A => @lem1032549 A a c b n d add mul n0 h1 h2 h3). Qed.
Lemma lem1032559 {A : Type'} (a : A) (b : A) (n : A) (add : type1400 A) (mul : type1400 A) (n0 : A) (h1 : term30 A add mul) (h2 : term31 A add) (h3 : term29 A mul n0) : term100 A n0 a add b mul n.
Proof. exact (fun c : A => @lem1032554 A a c b n add mul n0 h1 h2 h3). Qed.
Lemma lem1032564 {A : Type'} (a : A) (n : A) (add : type1400 A) (mul : type1400 A) (n0 : A) (h1 : term30 A add mul) (h2 : term31 A add) (h3 : term29 A mul n0) : term101 A n0 a add mul n.
Proof. exact (fun b : A => @lem1032559 A a b n add mul n0 h1 h2 h3). Qed.
Lemma lem1032569 {A : Type'} (n : A) (add : type1400 A) (mul : type1400 A) (n0 : A) (h1 : term30 A add mul) (h2 : term31 A add) (h3 : term29 A mul n0) : term102 A n0 add mul n.
Proof. exact (fun a : A => @lem1032564 A a n add mul n0 h1 h2 h3). Qed.
Lemma lem1032574 {A : Type'} (add : type1400 A) (mul : type1400 A) (n0 : A) (h1 : term30 A add mul) (h2 : term31 A add) (h3 : term29 A mul n0) : term60 A n0 add mul.
Proof. exact (fun n : A => @lem1032569 A n add mul n0 h1 h2 h3). Qed.
Lemma lem1032575 {A : Type'} (add : type1400 A) (mul : type1400 A) (n0 : A) (h1 : term30 A add mul) (h2 : term31 A add) (h3 : term29 A mul n0) : term61 A n0 add mul.
Proof. exact (EQ_MP (@lem1032360 A n0 add mul h1) (@lem1032574 A add mul n0 h1 h2 h3)). Qed.
Lemma lem1032576 {A : Type'} (n0 : A) (add : type1400 A) (mul : type1400 A) (h1 : term27 A n0 add mul) : term28 A add mul.
Proof. exact (proj2 (@lem1032162 A n0 add mul h1)). Qed.
Lemma lem1032577 {A : Type'} (n0 : A) (add : type1400 A) (mul : type1400 A) (h1 : term27 A n0 add mul) : term29 A mul n0.
Proof. exact (proj1 (@lem1032162 A n0 add mul h1)). Qed.
Lemma lem1032578 {A : Type'} (add : type1400 A) (mul : type1400 A) (h1 : term28 A add mul) : term30 A add mul.
Proof. exact (proj2 (@lem1032163 A add mul h1)). Qed.
Lemma lem1032579 {A : Type'} (add : type1400 A) (mul : type1400 A) (h1 : term28 A add mul) : term31 A add.
Proof. exact (proj1 (@lem1032163 A add mul h1)). Qed.
Lemma lem1032580 {A : Type'} (add : type1400 A) (mul : type1400 A) (n0 : A) (h1 : term30 A add mul) (h2 : term31 A add) (h3 : term29 A mul n0) : (term30 A add mul) = (term61 A n0 add mul).
Proof. exact (prop_ext (fun h4 : term30 A add mul => @lem1032575 A add mul n0 h1 h2 h3) (fun h4 : term61 A n0 add mul => @lem1032165 A add mul h1)). Qed.
Lemma lem1032581 {A : Type'} (add : type1400 A) (mul : type1400 A) (n0 : A) (h1 : term30 A add mul) (h2 : term31 A add) (h3 : term29 A mul n0) : term61 A n0 add mul.
Proof. exact (EQ_MP (@lem1032580 A add mul n0 h1 h2 h3) (@lem1032165 A add mul h1)). Qed.
Lemma lem1032582 {A : Type'} (add : type1400 A) (mul : type1400 A) (n0 : A) (h1 : term30 A add mul) (h2 : term31 A add) (h3 : term29 A mul n0) : (term31 A add) = (term61 A n0 add mul).
Proof. exact (prop_ext (fun h4 : term31 A add => @lem1032581 A add mul n0 h1 h2 h3) (fun h4 : term61 A n0 add mul => @lem1032166 A add h2)). Qed.
Lemma lem1032583 {A : Type'} (add : type1400 A) (mul : type1400 A) (n0 : A) (h1 : term30 A add mul) (h2 : term31 A add) (h3 : term29 A mul n0) : term61 A n0 add mul.
Proof. exact (EQ_MP (@lem1032582 A add mul n0 h1 h2 h3) (@lem1032166 A add h2)). Qed.
Lemma lem1032584 {A : Type'} (n0 : A) (add : type1400 A) (mul : type1400 A) (h1 : term31 A add) (h2 : term29 A mul n0) (h3 : term28 A add mul) : (term30 A add mul) = (term61 A n0 add mul).
Proof. exact (prop_ext (fun h4 : term30 A add mul => @lem1032583 A add mul n0 h4 h1 h2) (fun h4 : term61 A n0 add mul => @lem1032578 A add mul h3)). Qed.
Lemma lem1032585 {A : Type'} (n0 : A) (add : type1400 A) (mul : type1400 A) (h1 : term31 A add) (h2 : term29 A mul n0) (h3 : term28 A add mul) : term61 A n0 add mul.
Proof. exact (EQ_MP (@lem1032584 A n0 add mul h1 h2 h3) (@lem1032578 A add mul h3)). Qed.
Lemma lem1032586 {A : Type'} (n0 : A) (add : type1400 A) (mul : type1400 A) (h1 : term29 A mul n0) (h2 : term28 A add mul) : (term31 A add) = (term61 A n0 add mul).
Proof. exact (prop_ext (fun h3 : term31 A add => @lem1032585 A n0 add mul h3 h1 h2) (fun h3 : term61 A n0 add mul => @lem1032579 A add mul h2)). Qed.
Lemma lem1032587 {A : Type'} (n0 : A) (add : type1400 A) (mul : type1400 A) (h1 : term29 A mul n0) (h2 : term28 A add mul) : term61 A n0 add mul.
Proof. exact (EQ_MP (@lem1032586 A n0 add mul h1 h2) (@lem1032579 A add mul h2)). Qed.
Lemma lem1032588 {A : Type'} (n0 : A) (add : type1400 A) (mul : type1400 A) (h1 : term29 A mul n0) (h2 : term28 A add mul) : (term29 A mul n0) = (term61 A n0 add mul).
Proof. exact (prop_ext (fun h3 : term29 A mul n0 => @lem1032587 A n0 add mul h1 h2) (fun h3 : term61 A n0 add mul => @lem1032164 A mul n0 h1)). Qed.
Lemma lem1032589 {A : Type'} (n0 : A) (add : type1400 A) (mul : type1400 A) (h1 : term29 A mul n0) (h2 : term28 A add mul) : term61 A n0 add mul.
Proof. exact (EQ_MP (@lem1032588 A n0 add mul h1 h2) (@lem1032164 A mul n0 h1)). Qed.
Lemma lem1032590 {A : Type'} (n0 : A) (add : type1400 A) (mul : type1400 A) (h1 : term29 A mul n0) (h2 : term27 A n0 add mul) : (term28 A add mul) = (term61 A n0 add mul).
Proof. exact (prop_ext (fun h3 : term28 A add mul => @lem1032589 A n0 add mul h1 h3) (fun h3 : term61 A n0 add mul => @lem1032576 A n0 add mul h2)). Qed.
Lemma lem1032591 {A : Type'} (n0 : A) (add : type1400 A) (mul : type1400 A) (h1 : term29 A mul n0) (h2 : term27 A n0 add mul) : term61 A n0 add mul.
Proof. exact (EQ_MP (@lem1032590 A n0 add mul h1 h2) (@lem1032576 A n0 add mul h2)). Qed.
Lemma lem1032592 {A : Type'} (n0 : A) (add : type1400 A) (mul : type1400 A) (h1 : term27 A n0 add mul) : (term29 A mul n0) = (term61 A n0 add mul).
Proof. exact (prop_ext (fun h2 : term29 A mul n0 => @lem1032591 A n0 add mul h2 h1) (fun h2 : term61 A n0 add mul => @lem1032577 A n0 add mul h1)). Qed.
Lemma lem1032593 {A : Type'} (n0 : A) (add : type1400 A) (mul : type1400 A) (h1 : term27 A n0 add mul) : term61 A n0 add mul.
Proof. exact (EQ_MP (@lem1032592 A n0 add mul h1) (@lem1032577 A n0 add mul h1)). Qed.
Lemma lem1032594 {A : Type'} (n0 : A) (add : type1400 A) (mul : type1400 A) : term103 A n0 add mul.
Proof. exact (fun h0 : term27 A n0 add mul => @lem1032593 A n0 add mul h0). Qed.
Lemma lem1032599 {A : Type'} (add : type1400 A) (mul : type1400 A) : term104 A add mul.
Proof. exact (fun n0 : A => @lem1032594 A n0 add mul). Qed.
Lemma lem1032604 {A : Type'} (add : type1400 A) : term105 A add.
Proof. exact (fun mul : type1400 A => @lem1032599 A add mul). Qed.
Lemma lem1032609 {A : Type'} : term106 A.
Proof. exact (fun add : type1400 A => @lem1032604 A add). Qed.
