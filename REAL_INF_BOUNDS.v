Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_INF_BOUNDS_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import INF_spec.
Require Import MEMBER_NOT_EMPTY_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm129_spec.
Require Import thm1339577_spec.
Require Import thm137_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem5241001 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5241002 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5241003 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5241002 t1) (@lem5241001 t1)). Qed.
Lemma lem5241004 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5241003 t1 t2). Qed.
Lemma lem5241005 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5241006 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5241005 t1 t2) (@lem5241004 t1 t2)). Qed.
Lemma lem5241007 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5241006 t1 t2 t3). Qed.
Lemma lem5241008 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5241009 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5241008 t1 t2 t3) (@lem5241007 t1 t2 t3)). Qed.
Lemma lem5241010 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5241009 t1 t2 t3)). Qed.
Lemma lem5241012 {A : Type'} (s : A -> Prop) (h1 : (term7 A s) = (term8 A s)) : (term7 A s) = (term8 A s).
Proof. exact (h1). Qed.
Lemma lem5241013 {A : Type'} (s : A -> Prop) (h1 : (term7 A s) = (term8 A s)) : (term8 A s) = (term7 A s).
Proof. exact (SYM (@lem5241012 A s h1)). Qed.
Lemma lem5241014 {A : Type'} (s : A -> Prop) (h1 : (term8 A s) = (term7 A s)) : (term8 A s) = (term7 A s).
Proof. exact (h1). Qed.
Lemma lem5241015 {A : Type'} (s : A -> Prop) (h1 : (term8 A s) = (term7 A s)) : (term7 A s) = (term8 A s).
Proof. exact (SYM (@lem5241014 A s h1)). Qed.
Lemma lem5241016 {A : Type'} (s : A -> Prop) : ((term7 A s) = (term8 A s)) = ((term8 A s) = (term7 A s)).
Proof. exact (prop_ext (fun h1 : (term7 A s) = (term8 A s) => @lem5241013 A s h1) (fun h1 : (term8 A s) = (term7 A s) => @lem5241015 A s h1)). Qed.
Lemma lem5241017 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5241016 A s)). Qed.
Lemma lem5241018 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5241019 {A : Type'} : (term11 A) = (term12 A).
Proof. exact (MK_COMB (@lem5241018 A) (@lem5241017 A)). Qed.
Lemma lem5241020 {A : Type'} : term12 A.
Proof. exact (EQ_MP (@lem5241019 A) (@lem3216368 A)). Qed.
Lemma lem5241021 {A : Type'} (s : A -> Prop) : term13 A s.
Proof. exact (@lem5241020 A s). Qed.
Lemma lem5241022 {A : Type'} (s : A -> Prop) : (term13 A s) = ((term8 A s) = (term7 A s)).
Proof. exact (eq_refl (term13 A s)). Qed.
Lemma lem5241034 (s : real -> Prop) : term14 s.
Proof. exact (@lem5214027 s). Qed.
Lemma lem5241035 (s : real -> Prop) : (term14 s) = (term15 s).
Proof. exact (eq_refl (term14 s)). Qed.
Lemma lem5241036 (s : real -> Prop) : term15 s.
Proof. exact (EQ_MP (@lem5241035 s) (@lem5241034 s)). Qed.
Lemma lem5241037 (s : real -> Prop) (a : real) (b : real) (h1 : term16 s a b) : term16 s a b.
Proof. exact (h1). Qed.
Lemma lem5241038 (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term17 s a b.
Proof. exact (h1). Qed.
Lemma lem5241039 (s : real -> Prop) (h1 : term18 s) : term18 s.
Proof. exact (h1). Qed.
Lemma lem5241041 (p : Prop) (q : Prop) (r : Prop) : term19 p q r.
Proof. exact (@lem137 p q r (@lem129 p q r)). Qed.
Lemma lem5241042 (a : real) (s : real -> Prop) (b : real) : term20 a s b.
Proof. exact (@lem5241041 (term21 s) (term22 s) (term23 a s b)). Qed.
Lemma lem5241044 (p : Prop) : p = (term24 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5241045 (s : real -> Prop) : (term21 s) = (term25 s).
Proof. exact (@lem5241044 (term21 s)). Qed.
Lemma lem5241046 (s : real -> Prop) : (term25 s) = (term21 s).
Proof. exact (SYM (@lem5241045 s)). Qed.
Lemma lem5241047 (s : real -> Prop) (h1 : term26 s) : term26 s.
Proof. exact (h1). Qed.
Lemma lem5241050 (a : real) (b : real) (s : real -> Prop) (h1 : term27 a b s) : term27 a b s.
Proof. exact (h1). Qed.
Lemma lem5241051 (a : real) (b : real) (s : real -> Prop) : term28 a b s.
Proof. exact (fun h0 : term27 a b s => @lem5241050 a b s h0). Qed.
Lemma lem5241052 (a : real) (b : real) (s : real -> Prop) (h1 : term28 a b s) : term28 a b s.
Proof. exact (h1). Qed.
Lemma lem5241053 (a : real) (b : real) (s : real -> Prop) (h1 : term27 a b s) : term27 a b s.
Proof. exact (h1). Qed.
Lemma lem5241054 (a : real) (b : real) (s : real -> Prop) (h1 : term27 a b s) (h2 : term28 a b s) : term27 a b s.
Proof. exact (@lem5241052 a b s h2 (@lem5241053 a b s h1)). Qed.
Lemma lem5241055 (a : real) (b : real) (s : real -> Prop) (h1 : term27 a b s) : term29 a b s.
Proof. exact (fun h0 : term28 a b s => @lem5241054 a b s h1 h0). Qed.
Lemma lem5241056 (a : real) (b : real) (s : real -> Prop) (h1 : term28 a b s) : term28 a b s.
Proof. exact (h1). Qed.
Lemma lem5241057 (a : real) (b : real) (s : real -> Prop) (h1 : term27 a b s) (h2 : term28 a b s) : term27 a b s.
Proof. exact (@lem5241055 a b s h1 (@lem5241056 a b s h2)). Qed.
Lemma lem5241058 (a : real) (b : real) (s : real -> Prop) (h1 : term28 a b s) : term28 a b s.
Proof. exact (fun h0 : term27 a b s => @lem5241057 a b s h0 h1). Qed.
Lemma lem5241059 (a : real) (b : real) (s : real -> Prop) : term30 a b s.
Proof. exact (fun h0 : term28 a b s => @lem5241058 a b s h0). Qed.
Lemma lem5241062 (a : real) (b : real) (s : real -> Prop) : term28 a b s.
Proof. exact (@lem5241059 a b s (@lem5241051 a b s)). Qed.
Lemma lem5241088 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5241089 (s : real -> Prop) : (term25 s) = (term31 s).
Proof. exact (@lem5241088 (term26 s)). Qed.
Lemma lem5241091 (t : Prop) : (term32 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5241092 (s : real -> Prop) : (term31 s) = (term21 s).
Proof. exact (@lem5241091 (term21 s)). Qed.
Lemma lem5241095 (s : real -> Prop) : (term25 s) = (term21 s).
Proof. exact (TRANS (@lem5241089 s) (@lem5241092 s)). Qed.
Lemma lem5241106 (s : real -> Prop) (a : real) (b : real) : (term33 s a b) = (term33 s a b).
Proof. exact (eq_refl (term33 s a b)). Qed.
Lemma lem5241107 (a : real) (b : real) (s : real -> Prop) : (term34 a b s) = (term35 a b s).
Proof. exact (MK_COMB (@lem5241106 s a b) (@lem5241095 s)). Qed.
Lemma lem5241110 (s : real -> Prop) : (term36 s) = (term36 s).
Proof. exact (eq_refl (term36 s)). Qed.
Lemma lem5241111 (a : real) (b : real) (s : real -> Prop) : (term27 a b s) = (term37 a b s).
Proof. exact (MK_COMB (@lem5241110 s) (@lem5241107 a b s)). Qed.
Lemma lem5241114 (b : real) (s : real -> Prop) : (term38 b s) = (term39 b s).
Proof. exact (fun_ext (fun a : real => @lem5241111 a b s)). Qed.
Lemma lem5241115 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5241116 (b : real) (s : real -> Prop) : (term40 b s) = (term41 b s).
Proof. exact (MK_COMB (@lem5241115) (@lem5241114 b s)). Qed.
Lemma lem5241121 (s : real -> Prop) : (term42 s) = (term43 s).
Proof. exact (fun_ext (fun b : real => @lem5241116 b s)). Qed.
Lemma lem5241122 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5241123 (s : real -> Prop) : (term44 s) = (term45 s).
Proof. exact (MK_COMB (@lem5241122) (@lem5241121 s)). Qed.
Lemma lem5241128 : term46 = term47.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5241123 s)). Qed.
Lemma lem5241129 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5241138 : term48 = term49.
Proof. exact (MK_COMB (@lem5241129) (@lem5241128)). Qed.
Lemma lem5241143 (s : real -> Prop) (b : real) (x : real) : (term50 s b x) = (term50 s b x).
Proof. exact (eq_refl (term50 s b x)). Qed.
Lemma lem5241144 (s : real -> Prop) (b : real) : (term51 s b) = (term51 s b).
Proof. exact (fun_ext (fun x : real => @lem5241143 s b x)). Qed.
Lemma lem5241145 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5241146 (s : real -> Prop) (b : real) : (term52 s b) = (term52 s b).
Proof. exact (MK_COMB (@lem5241145) (@lem5241144 s b)). Qed.
Lemma lem5241147 (s : real -> Prop) : (term53 s) = (term53 s).
Proof. exact (fun_ext (fun b : real => @lem5241146 s b)). Qed.
Lemma lem5241148 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5241149 (s : real -> Prop) : (term54 s) = (term54 s).
Proof. exact (MK_COMB (@lem5241148) (@lem5241147 s)). Qed.
Lemma lem5241154 (s : real -> Prop) : (term55 s) = (term55 s).
Proof. exact (eq_refl (term55 s)). Qed.
Lemma lem5241155 (s : real -> Prop) : (term21 s) = (term21 s).
Proof. exact (MK_COMB (@lem5241154 s) (@lem5241149 s)). Qed.
Lemma lem5241164 (s : real -> Prop) (a : real) (x : real) (b : real) : (term56 s a x b) = (term56 s a x b).
Proof. exact (eq_refl (term56 s a x b)). Qed.
Lemma lem5241165 (s : real -> Prop) (a : real) (b : real) : (term57 s a b) = (term57 s a b).
Proof. exact (fun_ext (fun x : real => @lem5241164 s a x b)). Qed.
Lemma lem5241166 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5241167 (s : real -> Prop) (a : real) (b : real) : (term17 s a b) = (term17 s a b).
Proof. exact (MK_COMB (@lem5241166) (@lem5241165 s a b)). Qed.
Lemma lem5241168 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5241169 (s : real -> Prop) (a : real) (b : real) : (term33 s a b) = (term33 s a b).
Proof. exact (MK_COMB (@lem5241168) (@lem5241167 s a b)). Qed.
Lemma lem5241170 (a : real) (b : real) (s : real -> Prop) : (term35 a b s) = (term35 a b s).
Proof. exact (MK_COMB (@lem5241169 s a b) (@lem5241155 s)). Qed.
Lemma lem5241175 (s : real -> Prop) : (term36 s) = (term36 s).
Proof. exact (eq_refl (term36 s)). Qed.
Lemma lem5241176 (a : real) (b : real) (s : real -> Prop) : (term37 a b s) = (term37 a b s).
Proof. exact (MK_COMB (@lem5241175 s) (@lem5241170 a b s)). Qed.
Lemma lem5241177 (b : real) (s : real -> Prop) : (term39 b s) = (term39 b s).
Proof. exact (fun_ext (fun a : real => @lem5241176 a b s)). Qed.
Lemma lem5241178 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5241179 (b : real) (s : real -> Prop) : (term41 b s) = (term41 b s).
Proof. exact (MK_COMB (@lem5241178) (@lem5241177 b s)). Qed.
Lemma lem5241180 (s : real -> Prop) : (term43 s) = (term43 s).
Proof. exact (fun_ext (fun b : real => @lem5241179 b s)). Qed.
Lemma lem5241181 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5241182 (s : real -> Prop) : (term45 s) = (term45 s).
Proof. exact (MK_COMB (@lem5241181) (@lem5241180 s)). Qed.
Lemma lem5241183 : term47 = term47.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5241182 s)). Qed.
Lemma lem5241184 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5241185 : term49 = term49.
Proof. exact (MK_COMB (@lem5241184) (@lem5241183)). Qed.
Lemma lem5241236 : term48 = term49.
Proof. exact (TRANS (@lem5241138) (@lem5241185)). Qed.
Lemma lem5241237 : term49 = term48.
Proof. exact (SYM (@lem5241236)). Qed.
Lemma lem5241239 (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term17 s a b.
Proof. exact (h1). Qed.
Lemma lem5241241 (p : Prop) : p = (term24 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5241242 (s : real -> Prop) : (term21 s) = (term25 s).
Proof. exact (@lem5241241 (term21 s)). Qed.
Lemma lem5241243 (s : real -> Prop) : (term25 s) = (term21 s).
Proof. exact (SYM (@lem5241242 s)). Qed.
Lemma lem5241244 (s : real -> Prop) (h1 : term26 s) : term26 s.
Proof. exact (h1). Qed.
Lemma lem5241250 (s : real -> Prop) (h1 : term18 s) : term18 s.
Proof. exact (h1). Qed.
Lemma lem5241261 (s : real -> Prop) (a : real) (x : real) (b : real) : (term56 s a x b) = (term58 s a x b).
Proof. exact (@lem17265 (@IN real x s) (term59 a x b)). Qed.
Lemma lem5241262 (s : real -> Prop) (a : real) (b : real) : (term57 s a b) = (term60 s a b).
Proof. exact (fun_ext (fun x : real => @lem5241261 s a x b)). Qed.
Lemma lem5241263 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5241316 (s : real -> Prop) (a : real) (b : real) : (term17 s a b) = (term61 s a b).
Proof. exact (MK_COMB (@lem5241263) (@lem5241262 s a b)). Qed.
Lemma lem5241317 (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term61 s a b.
Proof. exact (EQ_MP (@lem5241316 s a b) (@lem5241239 s a b h1)). Qed.
Lemma lem5241320 (s : real -> Prop) : (term62 s) = (s = (@EMPTY real)).
Proof. exact (@lem16933 (s = (@EMPTY real))). Qed.
Lemma lem5241327 (s : real -> Prop) (b : real) (x : real) : (term63 s b x) = (term64 s b x).
Proof. exact (@lem17362 (@IN real x s) (real_le b x)). Qed.
Lemma lem5241328 (P : real -> Prop) : (term65 P) = (term66 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5241329 (s : real -> Prop) (b : real) : (term67 s b) = (term68 s b).
Proof. exact (@lem5241328 (term51 s b)). Qed.
Lemma lem5241330 (s : real -> Prop) (b : real) (x : real) : (term69 s b x) = (term50 s b x).
Proof. exact (eq_refl (term69 s b x)). Qed.
Lemma lem5241331 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5241332 (s : real -> Prop) (b : real) (x : real) : (term70 s b x) = (term63 s b x).
Proof. exact (MK_COMB (@lem5241331) (@lem5241330 s b x)). Qed.
Lemma lem5241333 (s : real -> Prop) (b : real) (x : real) : (term70 s b x) = (term64 s b x).
Proof. exact (TRANS (@lem5241332 s b x) (@lem5241327 s b x)). Qed.
Lemma lem5241334 (s : real -> Prop) (b : real) : (term71 s b) = (term72 s b).
Proof. exact (fun_ext (fun x : real => @lem5241333 s b x)). Qed.
Lemma lem5241335 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5241336 (s : real -> Prop) (b : real) : (term68 s b) = (term73 s b).
Proof. exact (MK_COMB (@lem5241335) (@lem5241334 s b)). Qed.
Lemma lem5241337 (s : real -> Prop) (b : real) : (term67 s b) = (term73 s b).
Proof. exact (TRANS (@lem5241329 s b) (@lem5241336 s b)). Qed.
Lemma lem5241338 (P : real -> Prop) : (term74 P) = (term75 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5241339 (s : real -> Prop) : (term76 s) = (term77 s).
Proof. exact (@lem5241338 (term53 s)). Qed.
Lemma lem5241340 (s : real -> Prop) (b : real) : (term78 s b) = (term52 s b).
Proof. exact (eq_refl (term78 s b)). Qed.
Lemma lem5241341 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5241342 (s : real -> Prop) (b : real) : (term79 s b) = (term67 s b).
Proof. exact (MK_COMB (@lem5241341) (@lem5241340 s b)). Qed.
Lemma lem5241343 (s : real -> Prop) (b : real) : (term79 s b) = (term73 s b).
Proof. exact (TRANS (@lem5241342 s b) (@lem5241337 s b)). Qed.
Lemma lem5241344 (s : real -> Prop) : (term80 s) = (term81 s).
Proof. exact (fun_ext (fun b : real => @lem5241343 s b)). Qed.
Lemma lem5241345 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5241346 (s : real -> Prop) : (term77 s) = (term82 s).
Proof. exact (MK_COMB (@lem5241345) (@lem5241344 s)). Qed.
Lemma lem5241347 (s : real -> Prop) : (term76 s) = (term82 s).
Proof. exact (TRANS (@lem5241339 s) (@lem5241346 s)). Qed.
Lemma lem5241348 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5241349 (s : real -> Prop) : (term83 s) = (term84 s).
Proof. exact (MK_COMB (@lem5241348) (@lem5241320 s)). Qed.
Lemma lem5241350 (s : real -> Prop) : (term85 s) = (term86 s).
Proof. exact (MK_COMB (@lem5241349 s) (@lem5241347 s)). Qed.
Lemma lem5241351 (s : real -> Prop) : (term26 s) = (term85 s).
Proof. exact (@lem17045 (term18 s) (term54 s)). Qed.
Lemma lem5241352 (s : real -> Prop) : (term26 s) = (term86 s).
Proof. exact (TRANS (@lem5241351 s) (@lem5241350 s)). Qed.
Lemma lem5241407 {A B : Type'} (P : type1413 A B) : (term87 A B P) = (term88 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5241408 (P : type1626) : (term89 P) = (term90 P).
Proof. exact (@lem5241407 real real P). Qed.
Lemma lem5241409 (s : real -> Prop) : (term91 s) = (term92 s).
Proof. exact (@lem5241408 (term93 s)). Qed.
Lemma lem5241410 (s : real -> Prop) (b : real) : (term94 s b) = (term72 s b).
Proof. exact (eq_refl (term94 s b)). Qed.
Lemma lem5241411 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5241412 (s : real -> Prop) (b : real) (x : real) : (term95 s b x) = (term96 s b x).
Proof. exact (MK_COMB (@lem5241410 s b) (@lem5241411 x)). Qed.
Lemma lem5241413 (s : real -> Prop) (b : real) (x : real) : (term96 s b x) = (term64 s b x).
Proof. exact (eq_refl (term96 s b x)). Qed.
Lemma lem5241414 (s : real -> Prop) (b : real) (x : real) : (term95 s b x) = (term64 s b x).
Proof. exact (TRANS (@lem5241412 s b x) (@lem5241413 s b x)). Qed.
Lemma lem5241415 (s : real -> Prop) (b : real) : (term97 s b) = (term72 s b).
Proof. exact (fun_ext (fun x : real => @lem5241414 s b x)). Qed.
Lemma lem5241416 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5241417 (s : real -> Prop) (b : real) : (term98 s b) = (term73 s b).
Proof. exact (MK_COMB (@lem5241416) (@lem5241415 s b)). Qed.
Lemma lem5241418 (s : real -> Prop) : (term99 s) = (term81 s).
Proof. exact (fun_ext (fun b : real => @lem5241417 s b)). Qed.
Lemma lem5241419 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5241420 (s : real -> Prop) : (term91 s) = (term82 s).
Proof. exact (MK_COMB (@lem5241419) (@lem5241418 s)). Qed.
Lemma lem5241421 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5241422 (s : real -> Prop) : (term100 s) = (term101 s).
Proof. exact (MK_COMB (@lem5241421) (@lem5241420 s)). Qed.
Lemma lem5241423 (s : real -> Prop) (b : real) : (term94 s b) = (term72 s b).
Proof. exact (eq_refl (term94 s b)). Qed.
Lemma lem5241424 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5241425 (s : real -> Prop) (x : real -> real) (b : real) : (term102 s x b) = (term103 s x b).
Proof. exact (MK_COMB (@lem5241423 s b) (@lem5241424 x b)). Qed.
Lemma lem5241426 (s : real -> Prop) (x : real -> real) (b : real) : (term103 s x b) = (term104 s x b).
Proof. exact (eq_refl (term103 s x b)). Qed.
Lemma lem5241427 (s : real -> Prop) (x : real -> real) (b : real) : (term102 s x b) = (term104 s x b).
Proof. exact (TRANS (@lem5241425 s x b) (@lem5241426 s x b)). Qed.
Lemma lem5241428 (s : real -> Prop) (x : real -> real) : (term105 s x) = (term106 s x).
Proof. exact (fun_ext (fun b : real => @lem5241427 s x b)). Qed.
Lemma lem5241429 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5241430 (s : real -> Prop) (x : real -> real) : (term107 s x) = (term108 s x).
Proof. exact (MK_COMB (@lem5241429) (@lem5241428 s x)). Qed.
Lemma lem5241431 (s : real -> Prop) : (term109 s) = (term110 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5241430 s x)). Qed.
Lemma lem5241432 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5241433 (s : real -> Prop) : (term92 s) = (term111 s).
Proof. exact (MK_COMB (@lem5241432) (@lem5241431 s)). Qed.
Lemma lem5241434 (s : real -> Prop) : ((term91 s) = (term92 s)) = ((term82 s) = (term111 s)).
Proof. exact (MK_COMB (@lem5241422 s) (@lem5241433 s)). Qed.
Lemma lem5241435 (s : real -> Prop) : (term82 s) = (term111 s).
Proof. exact (EQ_MP (@lem5241434 s) (@lem5241409 s)). Qed.
Lemma lem5241436 (s : real -> Prop) : (term84 s) = (term84 s).
Proof. exact (eq_refl (term84 s)). Qed.
Lemma lem5241437 (s : real -> Prop) : (term86 s) = (term112 s).
Proof. exact (MK_COMB (@lem5241436 s) (@lem5241435 s)). Qed.
Lemma lem5241439 {A : Type'} (P : Prop) (Q : A -> Prop) : (term113 A P Q) = (term114 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5241440 (P : Prop) (Q : type1028) : (term115 P Q) = (term116 P Q).
Proof. exact (@lem5241439 (real -> real) P Q). Qed.
Lemma lem5241441 (s : real -> Prop) : (term117 s) = (term118 s).
Proof. exact (@lem5241440 (s = (@EMPTY real)) (term110 s)). Qed.
Lemma lem5241442 (s : real -> Prop) (x : real -> real) : (term119 s x) = (term108 s x).
Proof. exact (eq_refl (term119 s x)). Qed.
Lemma lem5241443 (s : real -> Prop) : (term120 s) = (term110 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5241442 s x)). Qed.
Lemma lem5241444 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5241445 (s : real -> Prop) : (term121 s) = (term111 s).
Proof. exact (MK_COMB (@lem5241444) (@lem5241443 s)). Qed.
Lemma lem5241446 (s : real -> Prop) : (term84 s) = (term84 s).
Proof. exact (eq_refl (term84 s)). Qed.
Lemma lem5241447 (s : real -> Prop) : (term117 s) = (term112 s).
Proof. exact (MK_COMB (@lem5241446 s) (@lem5241445 s)). Qed.
Lemma lem5241448 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5241449 (s : real -> Prop) : (term122 s) = (term123 s).
Proof. exact (MK_COMB (@lem5241448) (@lem5241447 s)). Qed.
Lemma lem5241450 (s : real -> Prop) (x : real -> real) : (term119 s x) = (term108 s x).
Proof. exact (eq_refl (term119 s x)). Qed.
Lemma lem5241451 (s : real -> Prop) : (term84 s) = (term84 s).
Proof. exact (eq_refl (term84 s)). Qed.
Lemma lem5241452 (s : real -> Prop) (x : real -> real) : (term124 s x) = (term125 s x).
Proof. exact (MK_COMB (@lem5241451 s) (@lem5241450 s x)). Qed.
Lemma lem5241453 (s : real -> Prop) : (term126 s) = (term127 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5241452 s x)). Qed.
Lemma lem5241454 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5241455 (s : real -> Prop) : (term118 s) = (term128 s).
Proof. exact (MK_COMB (@lem5241454) (@lem5241453 s)). Qed.
Lemma lem5241456 (s : real -> Prop) : ((term117 s) = (term118 s)) = ((term112 s) = (term128 s)).
Proof. exact (MK_COMB (@lem5241449 s) (@lem5241455 s)). Qed.
Lemma lem5241457 (s : real -> Prop) : (term112 s) = (term128 s).
Proof. exact (EQ_MP (@lem5241456 s) (@lem5241441 s)). Qed.
Lemma lem5241459 (s : real -> Prop) : (term86 s) = (term128 s).
Proof. exact (TRANS (@lem5241437 s) (@lem5241457 s)). Qed.
Lemma lem5241460 (s : real -> Prop) : (term26 s) = (term128 s).
Proof. exact (TRANS (@lem5241352 s) (@lem5241459 s)). Qed.
Lemma lem5241461 (s : real -> Prop) (h1 : term26 s) : term128 s.
Proof. exact (EQ_MP (@lem5241460 s) (@lem5241244 s h1)). Qed.
Lemma lem5241462 (s : real -> Prop) (x : real -> real) (h1 : term125 s x) : term125 s x.
Proof. exact (h1). Qed.
Lemma lem5241470 (s : real -> Prop) (h1 : term18 s) : term18 s.
Proof. exact (h1). Qed.
Lemma lem5241493 (s : real -> Prop) (a : real) (x : real) (b : real) : (term58 s a x b) = (term58 s a x b).
Proof. exact (eq_refl (term58 s a x b)). Qed.
Lemma lem5241494 (s : real -> Prop) (a : real) (b : real) : (term60 s a b) = (term60 s a b).
Proof. exact (fun_ext (fun x : real => @lem5241493 s a x b)). Qed.
Lemma lem5241495 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5241496 (s : real -> Prop) (a : real) (b : real) : (term61 s a b) = (term61 s a b).
Proof. exact (MK_COMB (@lem5241495) (@lem5241494 s a b)). Qed.
Lemma lem5241497 (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term61 s a b.
Proof. exact (EQ_MP (@lem5241496 s a b) (@lem5241317 s a b h1)). Qed.
Lemma lem5241516 (s : real -> Prop) (x : real -> real) (b : real) : (term104 s x b) = (term104 s x b).
Proof. exact (eq_refl (term104 s x b)). Qed.
Lemma lem5241517 (s : real -> Prop) (x : real -> real) : (term106 s x) = (term106 s x).
Proof. exact (fun_ext (fun b : real => @lem5241516 s x b)). Qed.
Lemma lem5241518 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5241519 (s : real -> Prop) (x : real -> real) : (term108 s x) = (term108 s x).
Proof. exact (MK_COMB (@lem5241518) (@lem5241517 s x)). Qed.
Lemma lem5241526 (s : real -> Prop) : (term84 s) = (term84 s).
Proof. exact (eq_refl (term84 s)). Qed.
Lemma lem5241527 (s : real -> Prop) (x : real -> real) : (term125 s x) = (term125 s x).
Proof. exact (MK_COMB (@lem5241526 s) (@lem5241519 s x)). Qed.
Lemma lem5241528 (s : real -> Prop) (x : real -> real) (h1 : term125 s x) : term125 s x.
Proof. exact (EQ_MP (@lem5241527 s x) (@lem5241462 s x h1)). Qed.
Lemma lem5241530 (s : real -> Prop) (x : real -> real) (h1 : term108 s x) : term108 s x.
Proof. exact (h1). Qed.
Lemma lem5241534 (s : real -> Prop) (h1 : term18 s) : term18 s.
Proof. exact (h1). Qed.
Lemma lem5241561 (s : real -> Prop) (h1 : s = (@EMPTY real)) : s = (@EMPTY real).
Proof. exact (h1). Qed.
Lemma lem5241583 (a : real) (s : real -> Prop) (x : real) (b : real) : (term58 s a x b) = (term129 a s x b).
Proof. exact (@lem19490 (real_le a x) (term130 x s) (real_le x b)). Qed.
Lemma lem5241584 (a : real) (s : real -> Prop) (b : real) : (term60 s a b) = (term131 a s b).
Proof. exact (fun_ext (fun x : real => @lem5241583 a s x b)). Qed.
Lemma lem5241585 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5241587 (a : real) (s : real -> Prop) (b : real) : (term61 s a b) = (term132 a s b).
Proof. exact (MK_COMB (@lem5241585) (@lem5241584 a s b)). Qed.
Lemma lem5241588 (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term132 a s b.
Proof. exact (EQ_MP (@lem5241587 a s b) (@lem5241497 s a b h1)). Qed.
Lemma lem5241594 (s : real -> Prop) (x : real -> real) (b : real) : (term104 s x b) = (term104 s x b).
Proof. exact (eq_refl (term104 s x b)). Qed.
Lemma lem5241595 (s : real -> Prop) (x : real -> real) : (term106 s x) = (term106 s x).
Proof. exact (fun_ext (fun b : real => @lem5241594 s x b)). Qed.
Lemma lem5241596 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5241598 (s : real -> Prop) (x : real -> real) : (term108 s x) = (term108 s x).
Proof. exact (MK_COMB (@lem5241596) (@lem5241595 s x)). Qed.
Lemma lem5241599 (s : real -> Prop) (x : real -> real) (h1 : term108 s x) : term108 s x.
Proof. exact (EQ_MP (@lem5241598 s x) (@lem5241530 s x h1)). Qed.
Lemma lem5241603 (_68685 : real) (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term133 a s b _68685.
Proof. exact (@lem5241588 s a b h1 _68685). Qed.
Lemma lem5241604 (a : real) (s : real -> Prop) (_68685 : real) (b : real) : (term133 a s b _68685) = (term129 a s _68685 b).
Proof. exact (eq_refl (term133 a s b _68685)). Qed.
Lemma lem5241605 (_68685 : real) (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term129 a s _68685 b.
Proof. exact (EQ_MP (@lem5241604 a s _68685 b) (@lem5241603 _68685 s a b h1)). Qed.
Lemma lem5241606 (_68686 : real) (s : real -> Prop) (x : real -> real) (h1 : term108 s x) : term134 s x _68686.
Proof. exact (@lem5241599 s x h1 _68686). Qed.
Lemma lem5241607 (s : real -> Prop) (x : real -> real) (_68686 : real) : (term134 s x _68686) = (term104 s x _68686).
Proof. exact (eq_refl (term134 s x _68686)). Qed.
Lemma lem5241608 (_68686 : real) (s : real -> Prop) (x : real -> real) (h1 : term108 s x) : term104 s x _68686.
Proof. exact (EQ_MP (@lem5241607 s x _68686) (@lem5241606 _68686 s x h1)). Qed.
Lemma lem5241616 (s : real -> Prop) (h1 : term18 s) : term18 s.
Proof. exact (h1). Qed.
Lemma lem5241618 (s : real -> Prop) (h1 : s = (@EMPTY real)) : s = (@EMPTY real).
Proof. exact (h1). Qed.
Lemma lem5241636 (_68686 : real) (s : real -> Prop) (x : real -> real) (h1 : term108 s x) : term135 x _68686.
Proof. exact (proj2 (@lem5241608 _68686 s x h1)). Qed.
Lemma lem5241642 (_68685 : real) (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term136 s a _68685.
Proof. exact (proj1 (@lem5241605 _68685 s a b h1)). Qed.
Lemma lem5241663 : term137 = term137.
Proof. exact (eq_refl term137). Qed.
Lemma lem5241664 (s : real -> Prop) (h1 : s = (@EMPTY real)) : (term138 s) = term139.
Proof. exact (MK_COMB (@lem5241663) (@lem5241618 s h1)). Qed.
Lemma lem5241665 : term139 = term140.
Proof. exact (eq_refl term139). Qed.
Lemma lem5241666 (s : real -> Prop) : (term141 s) = (term141 s).
Proof. exact (eq_refl (term141 s)). Qed.
Lemma lem5241667 (s : real -> Prop) : ((term138 s) = term139) = ((term138 s) = term140).
Proof. exact (MK_COMB (@lem5241666 s) (@lem5241665)). Qed.
Lemma lem5241668 (s : real -> Prop) : (term138 s) = (term18 s).
Proof. exact (eq_refl (term138 s)). Qed.
Lemma lem5241669 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5241670 (s : real -> Prop) : (term141 s) = (term142 s).
Proof. exact (MK_COMB (@lem5241669) (@lem5241668 s)). Qed.
Lemma lem5241671 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem5241672 (s : real -> Prop) : ((term138 s) = term140) = ((term18 s) = term140).
Proof. exact (MK_COMB (@lem5241670 s) (@lem5241671)). Qed.
Lemma lem5241673 (s : real -> Prop) : ((term138 s) = term139) = ((term18 s) = term140).
Proof. exact (TRANS (@lem5241667 s) (@lem5241672 s)). Qed.
Lemma lem5241674 (s : real -> Prop) (h1 : s = (@EMPTY real)) : (term18 s) = term140.
Proof. exact (EQ_MP (@lem5241673 s) (@lem5241664 s h1)). Qed.
Lemma lem5241675 (s : real -> Prop) (h1 : term18 s) (h2 : s = (@EMPTY real)) : term140.
Proof. exact (EQ_MP (@lem5241674 s h2) (@lem5241616 s h1)). Qed.
Lemma lem5241745 (x : real -> Prop) : x = x.
Proof. exact (@lem21386 (real -> Prop) x). Qed.
Lemma lem5241746 : (@EMPTY real) = (@EMPTY real).
Proof. exact (@lem5241745 (@EMPTY real)). Qed.
Lemma lem5241747 : term143.
Proof. exact (fun h0 : term140 => @lem5241746). Qed.
Lemma lem5241749 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5241750 : term143 = ((@EMPTY real) = (@EMPTY real)).
Proof. exact (@lem5241749 ((@EMPTY real) = (@EMPTY real))). Qed.
Lemma lem5241751 : (@EMPTY real) = (@EMPTY real).
Proof. exact (EQ_MP (@lem5241750) (@lem5241747)). Qed.
Lemma lem5241754 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5241756 : term140 = term145.
Proof. exact (@lem5241754 ((@EMPTY real) = (@EMPTY real))). Qed.
Lemma lem5241759 (s : real -> Prop) (h1 : term18 s) (h2 : s = (@EMPTY real)) : term145.
Proof. exact (EQ_MP (@lem5241756) (@lem5241675 s h1 h2)). Qed.
Lemma lem5241762 (s : real -> Prop) (h1 : term18 s) (h2 : s = (@EMPTY real)) : False.
Proof. exact (@lem5241759 s h1 h2 (@lem5241751)). Qed.
Lemma lem5241763 (s : real -> Prop) (h1 : term18 s) (h2 : s = (@EMPTY real)) : term146.
Proof. exact (fun h0 : ~ False => @lem5241762 s h1 h2). Qed.
Lemma lem5241765 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5241766 : term146 = False.
Proof. exact (@lem5241765 False). Qed.
Lemma lem5241819 (_68686 : real) (s : real -> Prop) (x : real -> real) (h1 : term108 s x) : term147 x _68686 s.
Proof. exact (proj1 (@lem5241608 _68686 s x h1)). Qed.
Lemma lem5241820 (a : real) (s : real -> Prop) (x : real -> real) (h1 : term108 s x) : term147 x a s.
Proof. exact (@lem5241819 a s x h1). Qed.
Lemma lem5241821 (a : real) (s : real -> Prop) (x : real -> real) (h1 : term108 s x) : term148 x a s.
Proof. exact (fun h0 : term149 x a s => @lem5241820 a s x h1). Qed.
Lemma lem5241823 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5241824 (x : real -> real) (a : real) (s : real -> Prop) : (term148 x a s) = (term147 x a s).
Proof. exact (@lem5241823 (term147 x a s)). Qed.
Lemma lem5241825 (a : real) (s : real -> Prop) (x : real -> real) (h1 : term108 s x) : term147 x a s.
Proof. exact (EQ_MP (@lem5241824 x a s) (@lem5241821 a s x h1)). Qed.
Lemma lem5241831 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5241832 (a : real) (_68685 : real) (s : real -> Prop) : (term136 s a _68685) = (term150 a _68685 s).
Proof. exact (@lem5241831 (real_le a _68685) (term130 _68685 s)). Qed.
Lemma lem5241838 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5241839 (a : real) (_68685 : real) (s : real -> Prop) : (term151 s a _68685) = (term152 a _68685 s).
Proof. exact (MK_COMB (@lem5241838) (@lem5241832 a _68685 s)). Qed.
Lemma lem5241845 (a : real) (_68685 : real) (s : real -> Prop) : (term150 a _68685 s) = (term150 a _68685 s).
Proof. exact (eq_refl (term150 a _68685 s)). Qed.
Lemma lem5241846 (a : real) (_68685 : real) (s : real -> Prop) : ((term136 s a _68685) = (term150 a _68685 s)) = ((term150 a _68685 s) = (term150 a _68685 s)).
Proof. exact (MK_COMB (@lem5241839 a _68685 s) (@lem5241845 a _68685 s)). Qed.
Lemma lem5241848 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5241849 (x : Prop) : (x = x) = True.
Proof. exact (@lem5241848 Prop x). Qed.
Lemma lem5241850 (a : real) (_68685 : real) (s : real -> Prop) : ((term150 a _68685 s) = (term150 a _68685 s)) = True.
Proof. exact (@lem5241849 (term150 a _68685 s)). Qed.
Lemma lem5241851 (a : real) (_68685 : real) (s : real -> Prop) : ((term136 s a _68685) = (term150 a _68685 s)) = True.
Proof. exact (TRANS (@lem5241846 a _68685 s) (@lem5241850 a _68685 s)). Qed.
Lemma lem5241852 (a : real) (_68685 : real) (s : real -> Prop) : True = ((term136 s a _68685) = (term150 a _68685 s)).
Proof. exact (SYM (@lem5241851 a _68685 s)). Qed.
Lemma lem5241853 (a : real) (_68685 : real) (s : real -> Prop) : (term136 s a _68685) = (term150 a _68685 s).
Proof. exact (EQ_MP (@lem5241852 a _68685 s) (@lem0)). Qed.
Lemma lem5241854 (_68685 : real) (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term150 a _68685 s.
Proof. exact (EQ_MP (@lem5241853 a _68685 s) (@lem5241642 _68685 s a b h1)). Qed.
Lemma lem5241856 (b : Prop) (a : Prop) : (a \/ b) = (term153 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5241857 (s : real -> Prop) (a : real) (_68685 : real) : (term150 a _68685 s) = (term154 s a _68685).
Proof. exact (@lem5241856 (term130 _68685 s) (real_le a _68685)). Qed.
Lemma lem5241859 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5241860 (_68685 : real) (s : real -> Prop) : (term155 _68685 s) = (@IN real _68685 s).
Proof. exact (@lem5241859 (@IN real _68685 s)). Qed.
Lemma lem5241861 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5241862 (_68685 : real) (s : real -> Prop) : (term156 _68685 s) = (term157 _68685 s).
Proof. exact (MK_COMB (@lem5241861) (@lem5241860 _68685 s)). Qed.
Lemma lem5241863 (a : real) (_68685 : real) : (real_le a _68685) = (real_le a _68685).
Proof. exact (eq_refl (real_le a _68685)). Qed.
Lemma lem5241864 (s : real -> Prop) (a : real) (_68685 : real) : (term154 s a _68685) = (term50 s a _68685).
Proof. exact (MK_COMB (@lem5241862 _68685 s) (@lem5241863 a _68685)). Qed.
Lemma lem5241865 (s : real -> Prop) (a : real) (_68685 : real) : (term150 a _68685 s) = (term50 s a _68685).
Proof. exact (TRANS (@lem5241857 s a _68685) (@lem5241864 s a _68685)). Qed.
Lemma lem5241868 (_68685 : real) (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term50 s a _68685.
Proof. exact (EQ_MP (@lem5241865 s a _68685) (@lem5241854 _68685 s a b h1)). Qed.
Lemma lem5241869 (x : real -> real) (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term158 s x a.
Proof. exact (@lem5241868 (x a) s a b h1). Qed.
Lemma lem5241872 (x : real -> real) (s : real -> Prop) (a : real) (b : real) (h1 : term108 s x) (h2 : term17 s a b) : term159 x a.
Proof. exact (@lem5241869 x s a b h2 (@lem5241825 a s x h1)). Qed.
Lemma lem5241873 (x : real -> real) (s : real -> Prop) (a : real) (b : real) (h1 : term108 s x) (h2 : term17 s a b) : term160 x a.
Proof. exact (fun h0 : term135 x a => @lem5241872 x s a b h1 h2). Qed.
Lemma lem5241875 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5241876 (x : real -> real) (a : real) : (term160 x a) = (term159 x a).
Proof. exact (@lem5241875 (term159 x a)). Qed.
Lemma lem5241877 (x : real -> real) (s : real -> Prop) (a : real) (b : real) (h1 : term108 s x) (h2 : term17 s a b) : term159 x a.
Proof. exact (EQ_MP (@lem5241876 x a) (@lem5241873 x s a b h1 h2)). Qed.
Lemma lem5241880 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5241882 (x : real -> real) (_68686 : real) : (term135 x _68686) = (term161 x _68686).
Proof. exact (@lem5241880 (term159 x _68686)). Qed.
Lemma lem5241885 (_68686 : real) (s : real -> Prop) (x : real -> real) (h1 : term108 s x) : term161 x _68686.
Proof. exact (EQ_MP (@lem5241882 x _68686) (@lem5241636 _68686 s x h1)). Qed.
Lemma lem5241886 (a : real) (s : real -> Prop) (x : real -> real) (h1 : term108 s x) : term161 x a.
Proof. exact (@lem5241885 a s x h1). Qed.
Lemma lem5241889 (x : real -> real) (s : real -> Prop) (a : real) (b : real) (h1 : term108 s x) (h2 : term17 s a b) : False.
Proof. exact (@lem5241886 a s x h1 (@lem5241877 x s a b h1 h2)). Qed.
Lemma lem5241890 (x : real -> real) (s : real -> Prop) (a : real) (b : real) (h1 : term108 s x) (h2 : term17 s a b) : term146.
Proof. exact (fun h0 : ~ False => @lem5241889 x s a b h1 h2). Qed.
Lemma lem5241892 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5241893 : term146 = False.
Proof. exact (@lem5241892 False). Qed.
Lemma lem5241894 (x : real -> real) (s : real -> Prop) (a : real) (b : real) (h1 : term108 s x) (h2 : term17 s a b) : False.
Proof. exact (EQ_MP (@lem5241893) (@lem5241890 x s a b h1 h2)). Qed.
Lemma lem5241895 (s : real -> Prop) (h1 : term18 s) (h2 : s = (@EMPTY real)) : False.
Proof. exact (EQ_MP (@lem5241766) (@lem5241763 s h1 h2)). Qed.
Lemma lem5241896 (s : real -> Prop) (h1 : term18 s) (h2 : s = (@EMPTY real)) : (s = (@EMPTY real)) = False.
Proof. exact (prop_ext (fun h3 : s = (@EMPTY real) => @lem5241895 s h1 h2) (fun h3 : False => @lem5241618 s h2)). Qed.
Lemma lem5241897 (s : real -> Prop) (h1 : term18 s) (h2 : s = (@EMPTY real)) : False.
Proof. exact (EQ_MP (@lem5241896 s h1 h2) (@lem5241618 s h2)). Qed.
Lemma lem5241898 (s : real -> Prop) (h1 : term18 s) (h2 : s = (@EMPTY real)) : (term18 s) = False.
Proof. exact (prop_ext (fun h3 : term18 s => @lem5241897 s h1 h2) (fun h3 : False => @lem5241616 s h1)). Qed.
Lemma lem5241899 (s : real -> Prop) (h1 : term18 s) (h2 : s = (@EMPTY real)) : False.
Proof. exact (EQ_MP (@lem5241898 s h1 h2) (@lem5241616 s h1)). Qed.
Lemma lem5241900 (s : real -> Prop) (h1 : term18 s) (h2 : s = (@EMPTY real)) : (s = (@EMPTY real)) = False.
Proof. exact (prop_ext (fun h3 : s = (@EMPTY real) => @lem5241899 s h1 h2) (fun h3 : False => @lem5241561 s h2)). Qed.
Lemma lem5241901 (s : real -> Prop) (h1 : term18 s) (h2 : s = (@EMPTY real)) : False.
Proof. exact (EQ_MP (@lem5241900 s h1 h2) (@lem5241561 s h2)). Qed.
Lemma lem5241902 (s : real -> Prop) (h1 : term18 s) (h2 : s = (@EMPTY real)) : (term18 s) = False.
Proof. exact (prop_ext (fun h3 : term18 s => @lem5241901 s h1 h2) (fun h3 : False => @lem5241534 s h1)). Qed.
Lemma lem5241903 (s : real -> Prop) (h1 : term18 s) (h2 : s = (@EMPTY real)) : False.
Proof. exact (EQ_MP (@lem5241902 s h1 h2) (@lem5241534 s h1)). Qed.
Lemma lem5241904 (x : real -> real) (s : real -> Prop) (a : real) (b : real) (h1 : term108 s x) (h2 : term17 s a b) : (term108 s x) = False.
Proof. exact (prop_ext (fun h3 : term108 s x => @lem5241894 x s a b h1 h2) (fun h3 : False => @lem5241599 s x h1)). Qed.
Lemma lem5241905 (x : real -> real) (s : real -> Prop) (a : real) (b : real) (h1 : term108 s x) (h2 : term17 s a b) : False.
Proof. exact (EQ_MP (@lem5241904 x s a b h1 h2) (@lem5241599 s x h1)). Qed.
Lemma lem5241906 (s : real -> Prop) (h1 : term18 s) (h2 : s = (@EMPTY real)) : (s = (@EMPTY real)) = False.
Proof. exact (prop_ext (fun h3 : s = (@EMPTY real) => @lem5241903 s h1 h2) (fun h3 : False => @lem5241561 s h2)). Qed.
Lemma lem5241907 (s : real -> Prop) (h1 : term18 s) (h2 : s = (@EMPTY real)) : False.
Proof. exact (EQ_MP (@lem5241906 s h1 h2) (@lem5241561 s h2)). Qed.
Lemma lem5241908 (s : real -> Prop) (h1 : term18 s) (h2 : s = (@EMPTY real)) : (term18 s) = False.
Proof. exact (prop_ext (fun h3 : term18 s => @lem5241907 s h1 h2) (fun h3 : False => @lem5241534 s h1)). Qed.
Lemma lem5241909 (s : real -> Prop) (h1 : term18 s) (h2 : s = (@EMPTY real)) : False.
Proof. exact (EQ_MP (@lem5241908 s h1 h2) (@lem5241534 s h1)). Qed.
Lemma lem5241910 (a : real) (b : real) (s : real -> Prop) (x : real -> real) (h1 : term17 s a b) (h2 : term18 s) (h3 : term125 s x) : False.
Proof. exact (or_elim (@lem5241528 s x h3) (fun h0 : s = (@EMPTY real) => @lem5241909 s h2 h0) (fun h0 : term108 s x => @lem5241905 x s a b h0 h1)). Qed.
Lemma lem5241911 (a : real) (b : real) (s : real -> Prop) (x : real -> real) (h1 : term17 s a b) (h2 : term18 s) (h3 : term125 s x) : (term125 s x) = False.
Proof. exact (prop_ext (fun h4 : term125 s x => @lem5241910 a b s x h1 h2 h3) (fun h4 : False => @lem5241528 s x h3)). Qed.
Lemma lem5241912 (a : real) (b : real) (s : real -> Prop) (x : real -> real) (h1 : term17 s a b) (h2 : term18 s) (h3 : term125 s x) : False.
Proof. exact (EQ_MP (@lem5241911 a b s x h1 h2 h3) (@lem5241528 s x h3)). Qed.
Lemma lem5241913 (a : real) (b : real) (s : real -> Prop) (x : real -> real) (h1 : term17 s a b) (h2 : term18 s) (h3 : term125 s x) : (term18 s) = False.
Proof. exact (prop_ext (fun h4 : term18 s => @lem5241912 a b s x h1 h2 h3) (fun h4 : False => @lem5241470 s h2)). Qed.
Lemma lem5241914 (a : real) (b : real) (s : real -> Prop) (x : real -> real) (h1 : term17 s a b) (h2 : term18 s) (h3 : term125 s x) : False.
Proof. exact (EQ_MP (@lem5241913 a b s x h1 h2 h3) (@lem5241470 s h2)). Qed.
Lemma lem5241915 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term26 s) (h3 : term18 s) : False.
Proof. exact (ex_elim (@lem5241461 s h2) (fun x : real -> real => fun h0 : term127 s x => @lem5241914 a b s x h1 h3 h0)). Qed.
Lemma lem5241916 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term26 s) (h3 : term18 s) : (term18 s) = False.
Proof. exact (prop_ext (fun h4 : term18 s => @lem5241915 a b s h1 h2 h3) (fun h4 : False => @lem5241250 s h3)). Qed.
Lemma lem5241917 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term26 s) (h3 : term18 s) : False.
Proof. exact (EQ_MP (@lem5241916 a b s h1 h2 h3) (@lem5241250 s h3)). Qed.
Lemma lem5241918 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term26 s) (h3 : term18 s) : (term26 s) = False.
Proof. exact (prop_ext (fun h4 : term26 s => @lem5241917 a b s h1 h2 h3) (fun h4 : False => @lem5241244 s h2)). Qed.
Lemma lem5241919 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term26 s) (h3 : term18 s) : False.
Proof. exact (EQ_MP (@lem5241918 a b s h1 h2 h3) (@lem5241244 s h2)). Qed.
Lemma lem5241920 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term18 s) : term25 s.
Proof. exact (fun h0 : term26 s => @lem5241919 a b s h1 h0 h2). Qed.
Lemma lem5241921 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term18 s) : term21 s.
Proof. exact (EQ_MP (@lem5241243 s) (@lem5241920 a b s h1 h2)). Qed.
Lemma lem5241922 (a : real) (b : real) (s : real -> Prop) (h1 : term18 s) : term35 a b s.
Proof. exact (fun h0 : term17 s a b => @lem5241921 a b s h0 h1). Qed.
Lemma lem5241923 (a : real) (b : real) (s : real -> Prop) : term37 a b s.
Proof. exact (fun h0 : term18 s => @lem5241922 a b s h0). Qed.
Lemma lem5241928 (b : real) (s : real -> Prop) : term41 b s.
Proof. exact (fun a : real => @lem5241923 a b s). Qed.
Lemma lem5241933 (s : real -> Prop) : term45 s.
Proof. exact (fun b : real => @lem5241928 b s). Qed.
Lemma lem5241938 : term49.
Proof. exact (fun s : real -> Prop => @lem5241933 s). Qed.
Lemma lem5241939 : term48.
Proof. exact (EQ_MP (@lem5241237) (@lem5241938)). Qed.
Lemma lem5241940 (s : real -> Prop) : term162 s.
Proof. exact (@lem5241939 s). Qed.
Lemma lem5241941 (s : real -> Prop) : (term162 s) = (term44 s).
Proof. exact (eq_refl (term162 s)). Qed.
Lemma lem5241942 (s : real -> Prop) : term44 s.
Proof. exact (EQ_MP (@lem5241941 s) (@lem5241940 s)). Qed.
Lemma lem5241943 (s : real -> Prop) (b : real) : term163 s b.
Proof. exact (@lem5241942 s b). Qed.
Lemma lem5241944 (b : real) (s : real -> Prop) : (term163 s b) = (term40 b s).
Proof. exact (eq_refl (term163 s b)). Qed.
Lemma lem5241945 (b : real) (s : real -> Prop) : term40 b s.
Proof. exact (EQ_MP (@lem5241944 b s) (@lem5241943 s b)). Qed.
Lemma lem5241946 (b : real) (s : real -> Prop) (a : real) : term164 b s a.
Proof. exact (@lem5241945 b s a). Qed.
Lemma lem5241947 (a : real) (b : real) (s : real -> Prop) : (term164 b s a) = (term27 a b s).
Proof. exact (eq_refl (term164 b s a)). Qed.
Lemma lem5241948 (a : real) (b : real) (s : real -> Prop) : term27 a b s.
Proof. exact (EQ_MP (@lem5241947 a b s) (@lem5241946 b s a)). Qed.
Lemma lem5241950 (a : real) (b : real) (s : real -> Prop) : term27 a b s.
Proof. exact (@lem5241062 a b s (@lem5241948 a b s)). Qed.
Lemma lem5241951 (a : real) (b : real) (s : real -> Prop) (h1 : term18 s) : term34 a b s.
Proof. exact (@lem5241950 a b s (@lem5241039 s h1)). Qed.
Lemma lem5241952 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term18 s) : term25 s.
Proof. exact (@lem5241951 a b s h2 (@lem5241038 s a b h1)). Qed.
Lemma lem5241953 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term26 s) (h3 : term18 s) : False.
Proof. exact (@lem5241952 a b s h1 h3 (@lem5241047 s h2)). Qed.
Lemma lem5241954 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term26 s) (h3 : term18 s) : (term26 s) = False.
Proof. exact (prop_ext (fun h4 : term26 s => @lem5241953 a b s h1 h2 h3) (fun h4 : False => @lem5241047 s h2)). Qed.
Lemma lem5241955 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term26 s) (h3 : term18 s) : False.
Proof. exact (EQ_MP (@lem5241954 a b s h1 h2 h3) (@lem5241047 s h2)). Qed.
Lemma lem5241956 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term18 s) : term25 s.
Proof. exact (fun h0 : term26 s => @lem5241955 a b s h1 h0 h2). Qed.
Lemma lem5241957 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term18 s) : term21 s.
Proof. exact (EQ_MP (@lem5241046 s) (@lem5241956 a b s h1 h2)). Qed.
Lemma lem5241959 {A : Type'} (s : A -> Prop) : (term8 A s) = (term7 A s).
Proof. exact (EQ_MP (@lem5241022 A s) (@lem5241021 A s)). Qed.
Lemma lem5241960 (s : real -> Prop) : (term18 s) = (term165 s).
Proof. exact (@lem5241959 real s). Qed.
Lemma lem5241961 (s : real -> Prop) (h1 : term18 s) : term165 s.
Proof. exact (EQ_MP (@lem5241960 s) (@lem5241039 s h1)). Qed.
Lemma lem5241963 (p : Prop) : p = (term24 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5241964 (a : real) (s : real -> Prop) (b : real) : (term166 a s b) = (term167 a s b).
Proof. exact (@lem5241963 (term166 a s b)). Qed.
Lemma lem5241965 (a : real) (s : real -> Prop) (b : real) : (term167 a s b) = (term166 a s b).
Proof. exact (SYM (@lem5241964 a s b)). Qed.
Lemma lem5241966 (a : real) (s : real -> Prop) (b : real) (h1 : term168 a s b) : term168 a s b.
Proof. exact (h1). Qed.
Lemma lem5241969 (a : real) (s : real -> Prop) (b : real) (h1 : term169 a s b) : term169 a s b.
Proof. exact (h1). Qed.
Lemma lem5241970 (a : real) (s : real -> Prop) (b : real) : term170 a s b.
Proof. exact (fun h0 : term169 a s b => @lem5241969 a s b h0). Qed.
Lemma lem5241971 (a : real) (s : real -> Prop) (b : real) (h1 : term170 a s b) : term170 a s b.
Proof. exact (h1). Qed.
Lemma lem5241972 (a : real) (s : real -> Prop) (b : real) (h1 : term169 a s b) : term169 a s b.
Proof. exact (h1). Qed.
Lemma lem5241973 (a : real) (s : real -> Prop) (b : real) (h1 : term169 a s b) (h2 : term170 a s b) : term169 a s b.
Proof. exact (@lem5241971 a s b h2 (@lem5241972 a s b h1)). Qed.
Lemma lem5241974 (a : real) (s : real -> Prop) (b : real) (h1 : term169 a s b) : term171 a s b.
Proof. exact (fun h0 : term170 a s b => @lem5241973 a s b h1 h0). Qed.
Lemma lem5241975 (a : real) (s : real -> Prop) (b : real) (h1 : term170 a s b) : term170 a s b.
Proof. exact (h1). Qed.
Lemma lem5241976 (a : real) (s : real -> Prop) (b : real) (h1 : term169 a s b) (h2 : term170 a s b) : term169 a s b.
Proof. exact (@lem5241974 a s b h1 (@lem5241975 a s b h2)). Qed.
Lemma lem5241977 (a : real) (s : real -> Prop) (b : real) (h1 : term170 a s b) : term170 a s b.
Proof. exact (fun h0 : term169 a s b => @lem5241976 a s b h0 h1). Qed.
Lemma lem5241978 (a : real) (s : real -> Prop) (b : real) : term172 a s b.
Proof. exact (fun h0 : term170 a s b => @lem5241977 a s b h0). Qed.
Lemma lem5241981 (a : real) (s : real -> Prop) (b : real) : term170 a s b.
Proof. exact (@lem5241978 a s b (@lem5241970 a s b)). Qed.
Lemma lem5242037 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5242038 : term173 = term174.
Proof. exact (@lem5242037 term175). Qed.
Lemma lem5242055 (a : real) (s : real -> Prop) (b : real) : (term176 a s b) = (term176 a s b).
Proof. exact (eq_refl (term176 a s b)). Qed.
Lemma lem5242056 (a : real) (s : real -> Prop) (b : real) : (term177 a s b) = (term178 a s b).
Proof. exact (MK_COMB (@lem5242055 a s b) (@lem5242038)). Qed.
Lemma lem5242059 (s : real -> Prop) (a : real) (b : real) : (term33 s a b) = (term33 s a b).
Proof. exact (eq_refl (term33 s a b)). Qed.
Lemma lem5242060 (a : real) (s : real -> Prop) (b : real) : (term169 a s b) = (term179 a s b).
Proof. exact (MK_COMB (@lem5242059 s a b) (@lem5242056 a s b)). Qed.
Lemma lem5242063 (s : real -> Prop) (b : real) : (term180 s b) = (term181 s b).
Proof. exact (fun_ext (fun a : real => @lem5242060 a s b)). Qed.
Lemma lem5242064 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5242065 (s : real -> Prop) (b : real) : (term182 s b) = (term183 s b).
Proof. exact (MK_COMB (@lem5242064) (@lem5242063 s b)). Qed.
Lemma lem5242070 (b : real) : (term184 b) = (term185 b).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5242065 s b)). Qed.
Lemma lem5242071 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5242072 (b : real) : (term186 b) = (term187 b).
Proof. exact (MK_COMB (@lem5242071) (@lem5242070 b)). Qed.
Lemma lem5242077 : term188 = term189.
Proof. exact (fun_ext (fun b : real => @lem5242072 b)). Qed.
Lemma lem5242078 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5242087 : term190 = term191.
Proof. exact (MK_COMB (@lem5242078) (@lem5242077)). Qed.
Lemma lem5242096 (y : real) (x : real) (z : real) : (term192 y x z) = (term192 y x z).
Proof. exact (eq_refl (term192 y x z)). Qed.
Lemma lem5242097 (y : real) (x : real) : (term193 y x) = (term193 y x).
Proof. exact (fun_ext (fun z : real => @lem5242096 y x z)). Qed.
Lemma lem5242098 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5242099 (y : real) (x : real) : (term194 y x) = (term194 y x).
Proof. exact (MK_COMB (@lem5242098) (@lem5242097 y x)). Qed.
Lemma lem5242100 (x : real) : (term195 x) = (term195 x).
Proof. exact (fun_ext (fun y : real => @lem5242099 y x)). Qed.
Lemma lem5242101 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5242102 (x : real) : (term196 x) = (term196 x).
Proof. exact (MK_COMB (@lem5242101) (@lem5242100 x)). Qed.
Lemma lem5242103 : term197 = term197.
Proof. exact (fun_ext (fun x : real => @lem5242102 x)). Qed.
Lemma lem5242104 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5242105 : term175 = term175.
Proof. exact (MK_COMB (@lem5242104) (@lem5242103)). Qed.
Lemma lem5242106 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5242107 : term174 = term174.
Proof. exact (MK_COMB (@lem5242106) (@lem5242105)). Qed.
Lemma lem5242112 (a : real) (s : real -> Prop) (b : real) : (term23 a s b) = (term23 a s b).
Proof. exact (eq_refl (term23 a s b)). Qed.
Lemma lem5242113 (b : real) (s : real -> Prop) : (term198 b s) = (term198 b s).
Proof. exact (eq_refl (term198 b s)). Qed.
Lemma lem5242118 (s : real -> Prop) (b : real) (x : real) : (term50 s b x) = (term50 s b x).
Proof. exact (eq_refl (term50 s b x)). Qed.
Lemma lem5242119 (s : real -> Prop) (b : real) : (term51 s b) = (term51 s b).
Proof. exact (fun_ext (fun x : real => @lem5242118 s b x)). Qed.
Lemma lem5242120 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5242121 (s : real -> Prop) (b : real) : (term52 s b) = (term52 s b).
Proof. exact (MK_COMB (@lem5242120) (@lem5242119 s b)). Qed.
Lemma lem5242122 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5242123 (s : real -> Prop) (b : real) : (term199 s b) = (term199 s b).
Proof. exact (MK_COMB (@lem5242122) (@lem5242121 s b)). Qed.
Lemma lem5242124 (b : real) (s : real -> Prop) : (term200 b s) = (term200 b s).
Proof. exact (MK_COMB (@lem5242123 s b) (@lem5242113 b s)). Qed.
Lemma lem5242125 (s : real -> Prop) : (term201 s) = (term201 s).
Proof. exact (fun_ext (fun b : real => @lem5242124 b s)). Qed.
Lemma lem5242126 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5242127 (s : real -> Prop) : (term202 s) = (term202 s).
Proof. exact (MK_COMB (@lem5242126) (@lem5242125 s)). Qed.
Lemma lem5242132 (s : real -> Prop) (x : real) : (term203 s x) = (term203 s x).
Proof. exact (eq_refl (term203 s x)). Qed.
Lemma lem5242133 (s : real -> Prop) : (term204 s) = (term204 s).
Proof. exact (fun_ext (fun x : real => @lem5242132 s x)). Qed.
Lemma lem5242134 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5242135 (s : real -> Prop) : (term205 s) = (term205 s).
Proof. exact (MK_COMB (@lem5242134) (@lem5242133 s)). Qed.
Lemma lem5242136 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5242137 (s : real -> Prop) : (term206 s) = (term206 s).
Proof. exact (MK_COMB (@lem5242136) (@lem5242135 s)). Qed.
Lemma lem5242138 (s : real -> Prop) : (term22 s) = (term22 s).
Proof. exact (MK_COMB (@lem5242137 s) (@lem5242127 s)). Qed.
Lemma lem5242139 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5242140 (s : real -> Prop) : (term207 s) = (term207 s).
Proof. exact (MK_COMB (@lem5242139) (@lem5242138 s)). Qed.
Lemma lem5242141 (a : real) (s : real -> Prop) (b : real) : (term208 a s b) = (term208 a s b).
Proof. exact (MK_COMB (@lem5242140 s) (@lem5242112 a s b)). Qed.
Lemma lem5242142 (x : real) (s : real -> Prop) : (@IN real x s) = (@IN real x s).
Proof. exact (eq_refl (@IN real x s)). Qed.
Lemma lem5242143 (s : real -> Prop) : (term209 s) = (term209 s).
Proof. exact (fun_ext (fun x : real => @lem5242142 x s)). Qed.
Lemma lem5242144 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5242145 (s : real -> Prop) : (term165 s) = (term165 s).
Proof. exact (MK_COMB (@lem5242144) (@lem5242143 s)). Qed.
Lemma lem5242146 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5242147 (s : real -> Prop) : (term210 s) = (term210 s).
Proof. exact (MK_COMB (@lem5242146) (@lem5242145 s)). Qed.
Lemma lem5242148 (a : real) (s : real -> Prop) (b : real) : (term166 a s b) = (term166 a s b).
Proof. exact (MK_COMB (@lem5242147 s) (@lem5242141 a s b)). Qed.
Lemma lem5242149 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5242150 (a : real) (s : real -> Prop) (b : real) : (term168 a s b) = (term168 a s b).
Proof. exact (MK_COMB (@lem5242149) (@lem5242148 a s b)). Qed.
Lemma lem5242151 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5242152 (a : real) (s : real -> Prop) (b : real) : (term176 a s b) = (term176 a s b).
Proof. exact (MK_COMB (@lem5242151) (@lem5242150 a s b)). Qed.
Lemma lem5242153 (a : real) (s : real -> Prop) (b : real) : (term178 a s b) = (term178 a s b).
Proof. exact (MK_COMB (@lem5242152 a s b) (@lem5242107)). Qed.
Lemma lem5242162 (s : real -> Prop) (a : real) (x : real) (b : real) : (term56 s a x b) = (term56 s a x b).
Proof. exact (eq_refl (term56 s a x b)). Qed.
Lemma lem5242163 (s : real -> Prop) (a : real) (b : real) : (term57 s a b) = (term57 s a b).
Proof. exact (fun_ext (fun x : real => @lem5242162 s a x b)). Qed.
Lemma lem5242164 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5242165 (s : real -> Prop) (a : real) (b : real) : (term17 s a b) = (term17 s a b).
Proof. exact (MK_COMB (@lem5242164) (@lem5242163 s a b)). Qed.
Lemma lem5242166 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5242167 (s : real -> Prop) (a : real) (b : real) : (term33 s a b) = (term33 s a b).
Proof. exact (MK_COMB (@lem5242166) (@lem5242165 s a b)). Qed.
Lemma lem5242168 (a : real) (s : real -> Prop) (b : real) : (term179 a s b) = (term179 a s b).
Proof. exact (MK_COMB (@lem5242167 s a b) (@lem5242153 a s b)). Qed.
Lemma lem5242169 (s : real -> Prop) (b : real) : (term181 s b) = (term181 s b).
Proof. exact (fun_ext (fun a : real => @lem5242168 a s b)). Qed.
Lemma lem5242170 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5242171 (s : real -> Prop) (b : real) : (term183 s b) = (term183 s b).
Proof. exact (MK_COMB (@lem5242170) (@lem5242169 s b)). Qed.
Lemma lem5242172 (b : real) : (term185 b) = (term185 b).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5242171 s b)). Qed.
Lemma lem5242173 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5242174 (b : real) : (term187 b) = (term187 b).
Proof. exact (MK_COMB (@lem5242173) (@lem5242172 b)). Qed.
Lemma lem5242175 : term189 = term189.
Proof. exact (fun_ext (fun b : real => @lem5242174 b)). Qed.
Lemma lem5242176 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5242177 : term191 = term191.
Proof. exact (MK_COMB (@lem5242176) (@lem5242175)). Qed.
Lemma lem5242272 : term190 = term191.
Proof. exact (TRANS (@lem5242087) (@lem5242177)). Qed.
Lemma lem5242273 : term191 = term190.
Proof. exact (SYM (@lem5242272)). Qed.
Lemma lem5242274 (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term17 s a b.
Proof. exact (h1). Qed.
Lemma lem5242275 (a : real) (s : real -> Prop) (b : real) (h1 : term168 a s b) : term168 a s b.
Proof. exact (h1). Qed.
Lemma lem5242276 (h1 : term175) : term175.
Proof. exact (h1). Qed.
Lemma lem5242287 (s : real -> Prop) (a : real) (x : real) (b : real) : (term56 s a x b) = (term58 s a x b).
Proof. exact (@lem17265 (@IN real x s) (term59 a x b)). Qed.
Lemma lem5242288 (s : real -> Prop) (a : real) (b : real) : (term57 s a b) = (term60 s a b).
Proof. exact (fun_ext (fun x : real => @lem5242287 s a x b)). Qed.
Lemma lem5242289 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5242342 (s : real -> Prop) (a : real) (b : real) : (term17 s a b) = (term61 s a b).
Proof. exact (MK_COMB (@lem5242289) (@lem5242288 s a b)). Qed.
Lemma lem5242343 (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term61 s a b.
Proof. exact (EQ_MP (@lem5242342 s a b) (@lem5242274 s a b h1)). Qed.
Lemma lem5242344 (x : real) (s : real -> Prop) : (@IN real x s) = (@IN real x s).
Proof. exact (eq_refl (@IN real x s)). Qed.
Lemma lem5242345 (s : real -> Prop) : (term209 s) = (term209 s).
Proof. exact (fun_ext (fun x : real => @lem5242344 x s)). Qed.
Lemma lem5242346 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5242347 (s : real -> Prop) : (term165 s) = (term165 s).
Proof. exact (MK_COMB (@lem5242346) (@lem5242345 s)). Qed.
Lemma lem5242354 (s : real -> Prop) (x : real) : (term203 s x) = (term211 s x).
Proof. exact (@lem17265 (@IN real x s) (term212 s x)). Qed.
Lemma lem5242355 (s : real -> Prop) : (term204 s) = (term213 s).
Proof. exact (fun_ext (fun x : real => @lem5242354 s x)). Qed.
Lemma lem5242356 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5242357 (s : real -> Prop) : (term205 s) = (term214 s).
Proof. exact (MK_COMB (@lem5242356) (@lem5242355 s)). Qed.
Lemma lem5242364 (s : real -> Prop) (b : real) (x : real) : (term63 s b x) = (term64 s b x).
Proof. exact (@lem17362 (@IN real x s) (real_le b x)). Qed.
Lemma lem5242365 (P : real -> Prop) : (term65 P) = (term66 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5242366 (s : real -> Prop) (b : real) : (term67 s b) = (term68 s b).
Proof. exact (@lem5242365 (term51 s b)). Qed.
Lemma lem5242367 (s : real -> Prop) (b : real) (x : real) : (term69 s b x) = (term50 s b x).
Proof. exact (eq_refl (term69 s b x)). Qed.
Lemma lem5242368 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5242369 (s : real -> Prop) (b : real) (x : real) : (term70 s b x) = (term63 s b x).
Proof. exact (MK_COMB (@lem5242368) (@lem5242367 s b x)). Qed.
Lemma lem5242370 (s : real -> Prop) (b : real) (x : real) : (term70 s b x) = (term64 s b x).
Proof. exact (TRANS (@lem5242369 s b x) (@lem5242364 s b x)). Qed.
Lemma lem5242371 (s : real -> Prop) (b : real) : (term71 s b) = (term72 s b).
Proof. exact (fun_ext (fun x : real => @lem5242370 s b x)). Qed.
Lemma lem5242372 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5242373 (s : real -> Prop) (b : real) : (term68 s b) = (term73 s b).
Proof. exact (MK_COMB (@lem5242372) (@lem5242371 s b)). Qed.
Lemma lem5242374 (s : real -> Prop) (b : real) : (term67 s b) = (term73 s b).
Proof. exact (TRANS (@lem5242366 s b) (@lem5242373 s b)). Qed.
Lemma lem5242375 (b : real) (s : real -> Prop) : (term198 b s) = (term198 b s).
Proof. exact (eq_refl (term198 b s)). Qed.
Lemma lem5242376 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5242377 (s : real -> Prop) (b : real) : (term215 s b) = (term216 s b).
Proof. exact (MK_COMB (@lem5242376) (@lem5242374 s b)). Qed.
Lemma lem5242378 (b : real) (s : real -> Prop) : (term217 b s) = (term218 b s).
Proof. exact (MK_COMB (@lem5242377 s b) (@lem5242375 b s)). Qed.
Lemma lem5242379 (b : real) (s : real -> Prop) : (term200 b s) = (term217 b s).
Proof. exact (@lem17265 (term52 s b) (term198 b s)). Qed.
Lemma lem5242380 (b : real) (s : real -> Prop) : (term200 b s) = (term218 b s).
Proof. exact (TRANS (@lem5242379 b s) (@lem5242378 b s)). Qed.
Lemma lem5242381 (s : real -> Prop) : (term201 s) = (term219 s).
Proof. exact (fun_ext (fun b : real => @lem5242380 b s)). Qed.
Lemma lem5242382 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5242383 (s : real -> Prop) : (term202 s) = (term220 s).
Proof. exact (MK_COMB (@lem5242382) (@lem5242381 s)). Qed.
Lemma lem5242384 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5242385 (s : real -> Prop) : (term206 s) = (term221 s).
Proof. exact (MK_COMB (@lem5242384) (@lem5242357 s)). Qed.
Lemma lem5242386 (s : real -> Prop) : (term22 s) = (term222 s).
Proof. exact (MK_COMB (@lem5242385 s) (@lem5242383 s)). Qed.
Lemma lem5242393 (a : real) (s : real -> Prop) (b : real) : (term223 a s b) = (term224 a s b).
Proof. exact (@lem17045 (term198 a s) (term212 s b)). Qed.
Lemma lem5242394 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5242395 (s : real -> Prop) : (term225 s) = (term226 s).
Proof. exact (MK_COMB (@lem5242394) (@lem5242386 s)). Qed.
Lemma lem5242396 (a : real) (s : real -> Prop) (b : real) : (term227 a s b) = (term228 a s b).
Proof. exact (MK_COMB (@lem5242395 s) (@lem5242393 a s b)). Qed.
Lemma lem5242397 (a : real) (s : real -> Prop) (b : real) : (term229 a s b) = (term227 a s b).
Proof. exact (@lem17362 (term22 s) (term23 a s b)). Qed.
Lemma lem5242398 (a : real) (s : real -> Prop) (b : real) : (term229 a s b) = (term228 a s b).
Proof. exact (TRANS (@lem5242397 a s b) (@lem5242396 a s b)). Qed.
Lemma lem5242399 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5242400 (s : real -> Prop) : (term230 s) = (term230 s).
Proof. exact (MK_COMB (@lem5242399) (@lem5242347 s)). Qed.
Lemma lem5242401 (a : real) (s : real -> Prop) (b : real) : (term231 a s b) = (term232 a s b).
Proof. exact (MK_COMB (@lem5242400 s) (@lem5242398 a s b)). Qed.
Lemma lem5242402 (a : real) (s : real -> Prop) (b : real) : (term168 a s b) = (term231 a s b).
Proof. exact (@lem17362 (term165 s) (term208 a s b)). Qed.
Lemma lem5242403 (a : real) (s : real -> Prop) (b : real) : (term168 a s b) = (term232 a s b).
Proof. exact (TRANS (@lem5242402 a s b) (@lem5242401 a s b)). Qed.
Lemma lem5242554 {A : Type'} (P : A -> Prop) (Q : Prop) : (term233 A P Q) = (term234 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5242555 (P : real -> Prop) (Q : Prop) : (term235 P Q) = (term236 P Q).
Proof. exact (@lem5242554 real P Q). Qed.
Lemma lem5242556 (b : real) (s : real -> Prop) : (term237 b s) = (term238 b s).
Proof. exact (@lem5242555 (term72 s b) (term198 b s)). Qed.
Lemma lem5242557 (s : real -> Prop) (b : real) (x : real) : (term96 s b x) = (term64 s b x).
Proof. exact (eq_refl (term96 s b x)). Qed.
Lemma lem5242558 (s : real -> Prop) (b : real) : (term239 s b) = (term72 s b).
Proof. exact (fun_ext (fun x : real => @lem5242557 s b x)). Qed.
Lemma lem5242559 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5242560 (s : real -> Prop) (b : real) : (term240 s b) = (term73 s b).
Proof. exact (MK_COMB (@lem5242559) (@lem5242558 s b)). Qed.
Lemma lem5242561 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5242562 (s : real -> Prop) (b : real) : (term241 s b) = (term216 s b).
Proof. exact (MK_COMB (@lem5242561) (@lem5242560 s b)). Qed.
Lemma lem5242563 (b : real) (s : real -> Prop) : (term198 b s) = (term198 b s).
Proof. exact (eq_refl (term198 b s)). Qed.
Lemma lem5242564 (b : real) (s : real -> Prop) : (term237 b s) = (term218 b s).
Proof. exact (MK_COMB (@lem5242562 s b) (@lem5242563 b s)). Qed.
Lemma lem5242565 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5242566 (b : real) (s : real -> Prop) : (term242 b s) = (term243 b s).
Proof. exact (MK_COMB (@lem5242565) (@lem5242564 b s)). Qed.
Lemma lem5242567 (s : real -> Prop) (b : real) (x : real) : (term96 s b x) = (term64 s b x).
Proof. exact (eq_refl (term96 s b x)). Qed.
Lemma lem5242568 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5242569 (s : real -> Prop) (b : real) (x : real) : (term244 s b x) = (term245 s b x).
Proof. exact (MK_COMB (@lem5242568) (@lem5242567 s b x)). Qed.
Lemma lem5242570 (b : real) (s : real -> Prop) : (term198 b s) = (term198 b s).
Proof. exact (eq_refl (term198 b s)). Qed.
Lemma lem5242571 (x : real) (b : real) (s : real -> Prop) : (term246 x b s) = (term247 x b s).
Proof. exact (MK_COMB (@lem5242569 s b x) (@lem5242570 b s)). Qed.
Lemma lem5242572 (b : real) (s : real -> Prop) : (term248 b s) = (term249 b s).
Proof. exact (fun_ext (fun x : real => @lem5242571 x b s)). Qed.
Lemma lem5242573 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5242574 (b : real) (s : real -> Prop) : (term238 b s) = (term250 b s).
Proof. exact (MK_COMB (@lem5242573) (@lem5242572 b s)). Qed.
Lemma lem5242575 (b : real) (s : real -> Prop) : ((term237 b s) = (term238 b s)) = ((term218 b s) = (term250 b s)).
Proof. exact (MK_COMB (@lem5242566 b s) (@lem5242574 b s)). Qed.
Lemma lem5242576 (b : real) (s : real -> Prop) : (term218 b s) = (term250 b s).
Proof. exact (EQ_MP (@lem5242575 b s) (@lem5242556 b s)). Qed.
Lemma lem5242577 (s : real -> Prop) : (term219 s) = (term251 s).
Proof. exact (fun_ext (fun b : real => @lem5242576 b s)). Qed.
Lemma lem5242578 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5242579 (s : real -> Prop) : (term220 s) = (term252 s).
Proof. exact (MK_COMB (@lem5242578) (@lem5242577 s)). Qed.
Lemma lem5242581 {A B : Type'} (P : type1413 A B) : (term87 A B P) = (term88 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5242582 (P : type1626) : (term89 P) = (term90 P).
Proof. exact (@lem5242581 real real P). Qed.
Lemma lem5242583 (s : real -> Prop) : (term253 s) = (term254 s).
Proof. exact (@lem5242582 (term255 s)). Qed.
Lemma lem5242584 (b : real) (s : real -> Prop) : (term256 s b) = (term249 b s).
Proof. exact (eq_refl (term256 s b)). Qed.
Lemma lem5242585 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5242586 (b : real) (s : real -> Prop) (x : real) : (term257 s b x) = (term258 b s x).
Proof. exact (MK_COMB (@lem5242584 b s) (@lem5242585 x)). Qed.
Lemma lem5242587 (x : real) (b : real) (s : real -> Prop) : (term258 b s x) = (term247 x b s).
Proof. exact (eq_refl (term258 b s x)). Qed.
Lemma lem5242588 (x : real) (b : real) (s : real -> Prop) : (term257 s b x) = (term247 x b s).
Proof. exact (TRANS (@lem5242586 b s x) (@lem5242587 x b s)). Qed.
Lemma lem5242589 (b : real) (s : real -> Prop) : (term259 s b) = (term249 b s).
Proof. exact (fun_ext (fun x : real => @lem5242588 x b s)). Qed.
Lemma lem5242590 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5242591 (b : real) (s : real -> Prop) : (term260 s b) = (term250 b s).
Proof. exact (MK_COMB (@lem5242590) (@lem5242589 b s)). Qed.
Lemma lem5242592 (s : real -> Prop) : (term261 s) = (term251 s).
Proof. exact (fun_ext (fun b : real => @lem5242591 b s)). Qed.
Lemma lem5242593 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5242594 (s : real -> Prop) : (term253 s) = (term252 s).
Proof. exact (MK_COMB (@lem5242593) (@lem5242592 s)). Qed.
Lemma lem5242595 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5242596 (s : real -> Prop) : (term262 s) = (term263 s).
Proof. exact (MK_COMB (@lem5242595) (@lem5242594 s)). Qed.
Lemma lem5242597 (b : real) (s : real -> Prop) : (term256 s b) = (term249 b s).
Proof. exact (eq_refl (term256 s b)). Qed.
Lemma lem5242598 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5242599 (s : real -> Prop) (x : real -> real) (b : real) : (term264 s x b) = (term265 s x b).
Proof. exact (MK_COMB (@lem5242597 b s) (@lem5242598 x b)). Qed.
Lemma lem5242600 (x : real -> real) (b : real) (s : real -> Prop) : (term265 s x b) = (term266 x b s).
Proof. exact (eq_refl (term265 s x b)). Qed.
Lemma lem5242601 (x : real -> real) (b : real) (s : real -> Prop) : (term264 s x b) = (term266 x b s).
Proof. exact (TRANS (@lem5242599 s x b) (@lem5242600 x b s)). Qed.
Lemma lem5242602 (x : real -> real) (s : real -> Prop) : (term267 s x) = (term268 x s).
Proof. exact (fun_ext (fun b : real => @lem5242601 x b s)). Qed.
Lemma lem5242603 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5242604 (x : real -> real) (s : real -> Prop) : (term269 s x) = (term270 x s).
Proof. exact (MK_COMB (@lem5242603) (@lem5242602 x s)). Qed.
Lemma lem5242605 (s : real -> Prop) : (term271 s) = (term272 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5242604 x s)). Qed.
Lemma lem5242606 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5242607 (s : real -> Prop) : (term254 s) = (term273 s).
Proof. exact (MK_COMB (@lem5242606) (@lem5242605 s)). Qed.
Lemma lem5242608 (s : real -> Prop) : ((term253 s) = (term254 s)) = ((term252 s) = (term273 s)).
Proof. exact (MK_COMB (@lem5242596 s) (@lem5242607 s)). Qed.
Lemma lem5242609 (s : real -> Prop) : (term252 s) = (term273 s).
Proof. exact (EQ_MP (@lem5242608 s) (@lem5242583 s)). Qed.
Lemma lem5242610 (s : real -> Prop) : (term220 s) = (term273 s).
Proof. exact (TRANS (@lem5242579 s) (@lem5242609 s)). Qed.
Lemma lem5242611 (s : real -> Prop) : (term221 s) = (term221 s).
Proof. exact (eq_refl (term221 s)). Qed.
Lemma lem5242612 (s : real -> Prop) : (term222 s) = (term274 s).
Proof. exact (MK_COMB (@lem5242611 s) (@lem5242610 s)). Qed.
Lemma lem5242614 {A : Type'} (P : Prop) (Q : A -> Prop) : (term275 A P Q) = (term276 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5242615 (P : Prop) (Q : type1028) : (term277 P Q) = (term278 P Q).
Proof. exact (@lem5242614 (real -> real) P Q). Qed.
Lemma lem5242616 (s : real -> Prop) : (term279 s) = (term280 s).
Proof. exact (@lem5242615 (term214 s) (term272 s)). Qed.
Lemma lem5242617 (x : real -> real) (s : real -> Prop) : (term281 s x) = (term270 x s).
Proof. exact (eq_refl (term281 s x)). Qed.
Lemma lem5242618 (s : real -> Prop) : (term282 s) = (term272 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5242617 x s)). Qed.
Lemma lem5242619 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5242620 (s : real -> Prop) : (term283 s) = (term273 s).
Proof. exact (MK_COMB (@lem5242619) (@lem5242618 s)). Qed.
Lemma lem5242621 (s : real -> Prop) : (term221 s) = (term221 s).
Proof. exact (eq_refl (term221 s)). Qed.
Lemma lem5242622 (s : real -> Prop) : (term279 s) = (term274 s).
Proof. exact (MK_COMB (@lem5242621 s) (@lem5242620 s)). Qed.
Lemma lem5242623 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5242624 (s : real -> Prop) : (term284 s) = (term285 s).
Proof. exact (MK_COMB (@lem5242623) (@lem5242622 s)). Qed.
Lemma lem5242625 (x : real -> real) (s : real -> Prop) : (term281 s x) = (term270 x s).
Proof. exact (eq_refl (term281 s x)). Qed.
Lemma lem5242626 (s : real -> Prop) : (term221 s) = (term221 s).
Proof. exact (eq_refl (term221 s)). Qed.
Lemma lem5242627 (x : real -> real) (s : real -> Prop) : (term286 s x) = (term287 x s).
Proof. exact (MK_COMB (@lem5242626 s) (@lem5242625 x s)). Qed.
Lemma lem5242628 (s : real -> Prop) : (term288 s) = (term289 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5242627 x s)). Qed.
Lemma lem5242629 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5242630 (s : real -> Prop) : (term280 s) = (term290 s).
Proof. exact (MK_COMB (@lem5242629) (@lem5242628 s)). Qed.
Lemma lem5242631 (s : real -> Prop) : ((term279 s) = (term280 s)) = ((term274 s) = (term290 s)).
Proof. exact (MK_COMB (@lem5242624 s) (@lem5242630 s)). Qed.
Lemma lem5242632 (s : real -> Prop) : (term274 s) = (term290 s).
Proof. exact (EQ_MP (@lem5242631 s) (@lem5242616 s)). Qed.
Lemma lem5242633 (s : real -> Prop) : (term222 s) = (term290 s).
Proof. exact (TRANS (@lem5242612 s) (@lem5242632 s)). Qed.
Lemma lem5242634 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5242635 (s : real -> Prop) : (term226 s) = (term291 s).
Proof. exact (MK_COMB (@lem5242634) (@lem5242633 s)). Qed.
Lemma lem5242636 (a : real) (s : real -> Prop) (b : real) : (term224 a s b) = (term224 a s b).
Proof. exact (eq_refl (term224 a s b)). Qed.
Lemma lem5242637 (a : real) (s : real -> Prop) (b : real) : (term228 a s b) = (term292 a s b).
Proof. exact (MK_COMB (@lem5242635 s) (@lem5242636 a s b)). Qed.
Lemma lem5242639 {A : Type'} (P : A -> Prop) (Q : Prop) : (term293 A P Q) = (term294 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5242640 (P : type1028) (Q : Prop) : (term295 P Q) = (term296 P Q).
Proof. exact (@lem5242639 (real -> real) P Q). Qed.
Lemma lem5242641 (a : real) (s : real -> Prop) (b : real) : (term297 a s b) = (term298 a s b).
Proof. exact (@lem5242640 (term289 s) (term224 a s b)). Qed.
Lemma lem5242642 (x : real -> real) (s : real -> Prop) : (term299 s x) = (term287 x s).
Proof. exact (eq_refl (term299 s x)). Qed.
Lemma lem5242643 (s : real -> Prop) : (term300 s) = (term289 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5242642 x s)). Qed.
Lemma lem5242644 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5242645 (s : real -> Prop) : (term301 s) = (term290 s).
Proof. exact (MK_COMB (@lem5242644) (@lem5242643 s)). Qed.
Lemma lem5242646 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5242647 (s : real -> Prop) : (term302 s) = (term291 s).
Proof. exact (MK_COMB (@lem5242646) (@lem5242645 s)). Qed.
Lemma lem5242648 (a : real) (s : real -> Prop) (b : real) : (term224 a s b) = (term224 a s b).
Proof. exact (eq_refl (term224 a s b)). Qed.
Lemma lem5242649 (a : real) (s : real -> Prop) (b : real) : (term297 a s b) = (term292 a s b).
Proof. exact (MK_COMB (@lem5242647 s) (@lem5242648 a s b)). Qed.
Lemma lem5242650 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5242651 (a : real) (s : real -> Prop) (b : real) : (term303 a s b) = (term304 a s b).
Proof. exact (MK_COMB (@lem5242650) (@lem5242649 a s b)). Qed.
Lemma lem5242652 (x : real -> real) (s : real -> Prop) : (term299 s x) = (term287 x s).
Proof. exact (eq_refl (term299 s x)). Qed.
Lemma lem5242653 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5242654 (x : real -> real) (s : real -> Prop) : (term305 s x) = (term306 x s).
Proof. exact (MK_COMB (@lem5242653) (@lem5242652 x s)). Qed.
Lemma lem5242655 (a : real) (s : real -> Prop) (b : real) : (term224 a s b) = (term224 a s b).
Proof. exact (eq_refl (term224 a s b)). Qed.
Lemma lem5242656 (x : real -> real) (a : real) (s : real -> Prop) (b : real) : (term307 x a s b) = (term308 x a s b).
Proof. exact (MK_COMB (@lem5242654 x s) (@lem5242655 a s b)). Qed.
Lemma lem5242657 (a : real) (s : real -> Prop) (b : real) : (term309 a s b) = (term310 a s b).
Proof. exact (fun_ext (fun x : real -> real => @lem5242656 x a s b)). Qed.
Lemma lem5242658 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5242659 (a : real) (s : real -> Prop) (b : real) : (term298 a s b) = (term311 a s b).
Proof. exact (MK_COMB (@lem5242658) (@lem5242657 a s b)). Qed.
Lemma lem5242660 (a : real) (s : real -> Prop) (b : real) : ((term297 a s b) = (term298 a s b)) = ((term292 a s b) = (term311 a s b)).
Proof. exact (MK_COMB (@lem5242651 a s b) (@lem5242659 a s b)). Qed.
Lemma lem5242661 (a : real) (s : real -> Prop) (b : real) : (term292 a s b) = (term311 a s b).
Proof. exact (EQ_MP (@lem5242660 a s b) (@lem5242641 a s b)). Qed.
Lemma lem5242662 (a : real) (s : real -> Prop) (b : real) : (term228 a s b) = (term311 a s b).
Proof. exact (TRANS (@lem5242637 a s b) (@lem5242661 a s b)). Qed.
Lemma lem5242663 (s : real -> Prop) : (term230 s) = (term230 s).
Proof. exact (eq_refl (term230 s)). Qed.
Lemma lem5242664 (a : real) (s : real -> Prop) (b : real) : (term232 a s b) = (term312 a s b).
Proof. exact (MK_COMB (@lem5242663 s) (@lem5242662 a s b)). Qed.
Lemma lem5242666 {A : Type'} (P : A -> Prop) (Q : Prop) : (term293 A P Q) = (term294 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5242667 (P : real -> Prop) (Q : Prop) : (term313 P Q) = (term314 P Q).
Proof. exact (@lem5242666 real P Q). Qed.
Lemma lem5242668 (a : real) (s : real -> Prop) (b : real) : (term315 a s b) = (term316 a s b).
Proof. exact (@lem5242667 (term209 s) (term311 a s b)). Qed.
Lemma lem5242669 (x : real) (s : real -> Prop) : (term317 s x) = (@IN real x s).
Proof. exact (eq_refl (term317 s x)). Qed.
Lemma lem5242670 (s : real -> Prop) : (term318 s) = (term209 s).
Proof. exact (fun_ext (fun x : real => @lem5242669 x s)). Qed.
Lemma lem5242671 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5242672 (s : real -> Prop) : (term319 s) = (term165 s).
Proof. exact (MK_COMB (@lem5242671) (@lem5242670 s)). Qed.
Lemma lem5242673 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5242674 (s : real -> Prop) : (term320 s) = (term230 s).
Proof. exact (MK_COMB (@lem5242673) (@lem5242672 s)). Qed.
Lemma lem5242675 (a : real) (s : real -> Prop) (b : real) : (term311 a s b) = (term311 a s b).
Proof. exact (eq_refl (term311 a s b)). Qed.
Lemma lem5242676 (a : real) (s : real -> Prop) (b : real) : (term315 a s b) = (term312 a s b).
Proof. exact (MK_COMB (@lem5242674 s) (@lem5242675 a s b)). Qed.
Lemma lem5242677 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5242678 (a : real) (s : real -> Prop) (b : real) : (term321 a s b) = (term322 a s b).
Proof. exact (MK_COMB (@lem5242677) (@lem5242676 a s b)). Qed.
Lemma lem5242679 (x : real) (s : real -> Prop) : (term317 s x) = (@IN real x s).
Proof. exact (eq_refl (term317 s x)). Qed.
Lemma lem5242680 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5242681 (x : real) (s : real -> Prop) : (term323 s x) = (term324 x s).
Proof. exact (MK_COMB (@lem5242680) (@lem5242679 x s)). Qed.
Lemma lem5242682 (a : real) (s : real -> Prop) (b : real) : (term311 a s b) = (term311 a s b).
Proof. exact (eq_refl (term311 a s b)). Qed.
Lemma lem5242683 (x : real) (a : real) (s : real -> Prop) (b : real) : (term325 x a s b) = (term326 x a s b).
Proof. exact (MK_COMB (@lem5242681 x s) (@lem5242682 a s b)). Qed.
Lemma lem5242684 (a : real) (s : real -> Prop) (b : real) : (term327 a s b) = (term328 a s b).
Proof. exact (fun_ext (fun x : real => @lem5242683 x a s b)). Qed.
Lemma lem5242685 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5242686 (a : real) (s : real -> Prop) (b : real) : (term316 a s b) = (term329 a s b).
Proof. exact (MK_COMB (@lem5242685) (@lem5242684 a s b)). Qed.
Lemma lem5242687 (a : real) (s : real -> Prop) (b : real) : ((term315 a s b) = (term316 a s b)) = ((term312 a s b) = (term329 a s b)).
Proof. exact (MK_COMB (@lem5242678 a s b) (@lem5242686 a s b)). Qed.
Lemma lem5242688 (a : real) (s : real -> Prop) (b : real) : (term312 a s b) = (term329 a s b).
Proof. exact (EQ_MP (@lem5242687 a s b) (@lem5242668 a s b)). Qed.
Lemma lem5242690 {A : Type'} (P : Prop) (Q : A -> Prop) : (term275 A P Q) = (term276 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5242691 (P : Prop) (Q : type1028) : (term277 P Q) = (term278 P Q).
Proof. exact (@lem5242690 (real -> real) P Q). Qed.
Lemma lem5242692 (x : real) (a : real) (s : real -> Prop) (b : real) : (term330 x a s b) = (term331 x a s b).
Proof. exact (@lem5242691 (@IN real x s) (term310 a s b)). Qed.
Lemma lem5242693 (x : real -> real) (a : real) (s : real -> Prop) (b : real) : (term332 a s b x) = (term308 x a s b).
Proof. exact (eq_refl (term332 a s b x)). Qed.
Lemma lem5242694 (a : real) (s : real -> Prop) (b : real) : (term333 a s b) = (term310 a s b).
Proof. exact (fun_ext (fun x : real -> real => @lem5242693 x a s b)). Qed.
Lemma lem5242695 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5242696 (a : real) (s : real -> Prop) (b : real) : (term334 a s b) = (term311 a s b).
Proof. exact (MK_COMB (@lem5242695) (@lem5242694 a s b)). Qed.
Lemma lem5242697 (x : real) (s : real -> Prop) : (term324 x s) = (term324 x s).
Proof. exact (eq_refl (term324 x s)). Qed.
Lemma lem5242698 (x : real) (a : real) (s : real -> Prop) (b : real) : (term330 x a s b) = (term326 x a s b).
Proof. exact (MK_COMB (@lem5242697 x s) (@lem5242696 a s b)). Qed.
Lemma lem5242699 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5242700 (x : real) (a : real) (s : real -> Prop) (b : real) : (term335 x a s b) = (term336 x a s b).
Proof. exact (MK_COMB (@lem5242699) (@lem5242698 x a s b)). Qed.
Lemma lem5242701 (x : real -> real) (a : real) (s : real -> Prop) (b : real) : (term332 a s b x) = (term308 x a s b).
Proof. exact (eq_refl (term332 a s b x)). Qed.
Lemma lem5242702 (x : real) (s : real -> Prop) : (term324 x s) = (term324 x s).
Proof. exact (eq_refl (term324 x s)). Qed.
Lemma lem5242703 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) : (term337 x a s b x') = (term338 x x' a s b).
Proof. exact (MK_COMB (@lem5242702 x s) (@lem5242701 x' a s b)). Qed.
Lemma lem5242704 (x : real) (a : real) (s : real -> Prop) (b : real) : (term339 x a s b) = (term340 x a s b).
Proof. exact (fun_ext (fun x' : real -> real => @lem5242703 x x' a s b)). Qed.
Lemma lem5242705 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5242706 (x : real) (a : real) (s : real -> Prop) (b : real) : (term331 x a s b) = (term341 x a s b).
Proof. exact (MK_COMB (@lem5242705) (@lem5242704 x a s b)). Qed.
Lemma lem5242707 (x : real) (a : real) (s : real -> Prop) (b : real) : ((term330 x a s b) = (term331 x a s b)) = ((term326 x a s b) = (term341 x a s b)).
Proof. exact (MK_COMB (@lem5242700 x a s b) (@lem5242706 x a s b)). Qed.
Lemma lem5242708 (x : real) (a : real) (s : real -> Prop) (b : real) : (term326 x a s b) = (term341 x a s b).
Proof. exact (EQ_MP (@lem5242707 x a s b) (@lem5242692 x a s b)). Qed.
Lemma lem5242709 (a : real) (s : real -> Prop) (b : real) : (term328 a s b) = (term342 a s b).
Proof. exact (fun_ext (fun x : real => @lem5242708 x a s b)). Qed.
Lemma lem5242710 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5242711 (a : real) (s : real -> Prop) (b : real) : (term329 a s b) = (term343 a s b).
Proof. exact (MK_COMB (@lem5242710) (@lem5242709 a s b)). Qed.
Lemma lem5242712 (a : real) (s : real -> Prop) (b : real) : (term312 a s b) = (term343 a s b).
Proof. exact (TRANS (@lem5242688 a s b) (@lem5242711 a s b)). Qed.
Lemma lem5242714 (a : real) (s : real -> Prop) (b : real) : (term232 a s b) = (term343 a s b).
Proof. exact (TRANS (@lem5242664 a s b) (@lem5242712 a s b)). Qed.
Lemma lem5242715 (a : real) (s : real -> Prop) (b : real) : (term168 a s b) = (term343 a s b).
Proof. exact (TRANS (@lem5242403 a s b) (@lem5242714 a s b)). Qed.
Lemma lem5242716 (a : real) (s : real -> Prop) (b : real) (h1 : term168 a s b) : term343 a s b.
Proof. exact (EQ_MP (@lem5242715 a s b) (@lem5242275 a s b h1)). Qed.
Lemma lem5242723 (x : real) (y : real) (z : real) : (term344 x y z) = (term345 x y z).
Proof. exact (@lem17045 (real_le x y) (real_le y z)). Qed.
Lemma lem5242724 (x : real) (z : real) : (real_le x z) = (real_le x z).
Proof. exact (eq_refl (real_le x z)). Qed.
Lemma lem5242725 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5242726 (x : real) (y : real) (z : real) : (term346 x y z) = (term347 x y z).
Proof. exact (MK_COMB (@lem5242725) (@lem5242723 x y z)). Qed.
Lemma lem5242727 (y : real) (x : real) (z : real) : (term348 y x z) = (term349 y x z).
Proof. exact (MK_COMB (@lem5242726 x y z) (@lem5242724 x z)). Qed.
Lemma lem5242728 (y : real) (x : real) (z : real) : (term192 y x z) = (term348 y x z).
Proof. exact (@lem17265 (term59 x y z) (real_le x z)). Qed.
Lemma lem5242729 (y : real) (x : real) (z : real) : (term192 y x z) = (term349 y x z).
Proof. exact (TRANS (@lem5242728 y x z) (@lem5242727 y x z)). Qed.
Lemma lem5242730 (y : real) (x : real) : (term193 y x) = (term350 y x).
Proof. exact (fun_ext (fun z : real => @lem5242729 y x z)). Qed.
Lemma lem5242731 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5242732 (y : real) (x : real) : (term194 y x) = (term351 y x).
Proof. exact (MK_COMB (@lem5242731) (@lem5242730 y x)). Qed.
Lemma lem5242733 (x : real) : (term195 x) = (term352 x).
Proof. exact (fun_ext (fun y : real => @lem5242732 y x)). Qed.
Lemma lem5242734 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5242735 (x : real) : (term196 x) = (term353 x).
Proof. exact (MK_COMB (@lem5242734) (@lem5242733 x)). Qed.
Lemma lem5242736 : term197 = term354.
Proof. exact (fun_ext (fun x : real => @lem5242735 x)). Qed.
Lemma lem5242737 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5242798 : term175 = term355.
Proof. exact (MK_COMB (@lem5242737) (@lem5242736)). Qed.
Lemma lem5242799 (h1 : term175) : term355.
Proof. exact (EQ_MP (@lem5242798) (@lem5242276 h1)). Qed.
Lemma lem5242800 (x : real) (a : real) (s : real -> Prop) (b : real) (h1 : term341 x a s b) : term341 x a s b.
Proof. exact (h1). Qed.
Lemma lem5242801 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term338 x x' a s b.
Proof. exact (h1). Qed.
Lemma lem5242824 (s : real -> Prop) (a : real) (x : real) (b : real) : (term58 s a x b) = (term58 s a x b).
Proof. exact (eq_refl (term58 s a x b)). Qed.
Lemma lem5242825 (s : real -> Prop) (a : real) (b : real) : (term60 s a b) = (term60 s a b).
Proof. exact (fun_ext (fun x : real => @lem5242824 s a x b)). Qed.
Lemma lem5242826 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5242827 (s : real -> Prop) (a : real) (b : real) : (term61 s a b) = (term61 s a b).
Proof. exact (MK_COMB (@lem5242826) (@lem5242825 s a b)). Qed.
Lemma lem5242828 (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term61 s a b.
Proof. exact (EQ_MP (@lem5242827 s a b) (@lem5242343 s a b h1)). Qed.
Lemma lem5242853 (y : real) (x : real) (z : real) : (term349 y x z) = (term349 y x z).
Proof. exact (eq_refl (term349 y x z)). Qed.
Lemma lem5242854 (y : real) (x : real) : (term350 y x) = (term350 y x).
Proof. exact (fun_ext (fun z : real => @lem5242853 y x z)). Qed.
Lemma lem5242855 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5242856 (y : real) (x : real) : (term351 y x) = (term351 y x).
Proof. exact (MK_COMB (@lem5242855) (@lem5242854 y x)). Qed.
Lemma lem5242857 (x : real) : (term352 x) = (term352 x).
Proof. exact (fun_ext (fun y : real => @lem5242856 y x)). Qed.
Lemma lem5242858 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5242859 (x : real) : (term353 x) = (term353 x).
Proof. exact (MK_COMB (@lem5242858) (@lem5242857 x)). Qed.
Lemma lem5242860 : term354 = term354.
Proof. exact (fun_ext (fun x : real => @lem5242859 x)). Qed.
Lemma lem5242861 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5242862 : term355 = term355.
Proof. exact (MK_COMB (@lem5242861) (@lem5242860)). Qed.
Lemma lem5242863 (h1 : term175) : term355.
Proof. exact (EQ_MP (@lem5242862) (@lem5242799 h1)). Qed.
Lemma lem5242884 (a : real) (s : real -> Prop) (b : real) : (term224 a s b) = (term224 a s b).
Proof. exact (eq_refl (term224 a s b)). Qed.
Lemma lem5242913 (x' : real -> real) (b : real) (s : real -> Prop) : (term266 x' b s) = (term266 x' b s).
Proof. exact (eq_refl (term266 x' b s)). Qed.
Lemma lem5242914 (x' : real -> real) (s : real -> Prop) : (term268 x' s) = (term268 x' s).
Proof. exact (fun_ext (fun b : real => @lem5242913 x' b s)). Qed.
Lemma lem5242915 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5242916 (x' : real -> real) (s : real -> Prop) : (term270 x' s) = (term270 x' s).
Proof. exact (MK_COMB (@lem5242915) (@lem5242914 x' s)). Qed.
Lemma lem5242933 (s : real -> Prop) (x : real) : (term211 s x) = (term211 s x).
Proof. exact (eq_refl (term211 s x)). Qed.
Lemma lem5242934 (s : real -> Prop) : (term213 s) = (term213 s).
Proof. exact (fun_ext (fun x : real => @lem5242933 s x)). Qed.
Lemma lem5242935 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5242936 (s : real -> Prop) : (term214 s) = (term214 s).
Proof. exact (MK_COMB (@lem5242935) (@lem5242934 s)). Qed.
Lemma lem5242937 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5242938 (s : real -> Prop) : (term221 s) = (term221 s).
Proof. exact (MK_COMB (@lem5242937) (@lem5242936 s)). Qed.
Lemma lem5242939 (x' : real -> real) (s : real -> Prop) : (term287 x' s) = (term287 x' s).
Proof. exact (MK_COMB (@lem5242938 s) (@lem5242916 x' s)). Qed.
Lemma lem5242940 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5242941 (x' : real -> real) (s : real -> Prop) : (term306 x' s) = (term306 x' s).
Proof. exact (MK_COMB (@lem5242940) (@lem5242939 x' s)). Qed.
Lemma lem5242942 (x' : real -> real) (a : real) (s : real -> Prop) (b : real) : (term308 x' a s b) = (term308 x' a s b).
Proof. exact (MK_COMB (@lem5242941 x' s) (@lem5242884 a s b)). Qed.
Lemma lem5242949 (x : real) (s : real -> Prop) : (term324 x s) = (term324 x s).
Proof. exact (eq_refl (term324 x s)). Qed.
Lemma lem5242950 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) : (term338 x x' a s b) = (term338 x x' a s b).
Proof. exact (MK_COMB (@lem5242949 x s) (@lem5242942 x' a s b)). Qed.
Lemma lem5242951 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term338 x x' a s b.
Proof. exact (EQ_MP (@lem5242950 x x' a s b) (@lem5242801 x x' a s b h1)). Qed.
Lemma lem5242952 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term308 x' a s b.
Proof. exact (proj2 (@lem5242951 x x' a s b h1)). Qed.
Lemma lem5242954 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term224 a s b.
Proof. exact (proj2 (@lem5242952 x x' a s b h1)). Qed.
Lemma lem5242955 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term287 x' s.
Proof. exact (proj1 (@lem5242952 x x' a s b h1)). Qed.
Lemma lem5242956 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term270 x' s.
Proof. exact (proj2 (@lem5242955 x x' a s b h1)). Qed.
Lemma lem5242957 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term214 s.
Proof. exact (proj1 (@lem5242955 x x' a s b h1)). Qed.
Lemma lem5242977 (a : real) (s : real -> Prop) (x : real) (b : real) : (term58 s a x b) = (term129 a s x b).
Proof. exact (@lem19490 (real_le a x) (term130 x s) (real_le x b)). Qed.
Lemma lem5242978 (a : real) (s : real -> Prop) (b : real) : (term60 s a b) = (term131 a s b).
Proof. exact (fun_ext (fun x : real => @lem5242977 a s x b)). Qed.
Lemma lem5242979 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5242981 (a : real) (s : real -> Prop) (b : real) : (term61 s a b) = (term132 a s b).
Proof. exact (MK_COMB (@lem5242979) (@lem5242978 a s b)). Qed.
Lemma lem5242982 (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term132 a s b.
Proof. exact (EQ_MP (@lem5242981 a s b) (@lem5242828 s a b h1)). Qed.
Lemma lem5243042 (x' : real -> real) (b : real) (s : real -> Prop) : (term266 x' b s) = (term356 x' b s).
Proof. exact (@lem19699 (term147 x' b s) (term135 x' b) (term198 b s)). Qed.
Lemma lem5243043 (x' : real -> real) (s : real -> Prop) : (term268 x' s) = (term357 x' s).
Proof. exact (fun_ext (fun b : real => @lem5243042 x' b s)). Qed.
Lemma lem5243044 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5243046 (x' : real -> real) (s : real -> Prop) : (term270 x' s) = (term358 x' s).
Proof. exact (MK_COMB (@lem5243044) (@lem5243043 x' s)). Qed.
Lemma lem5243047 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term358 x' s.
Proof. exact (EQ_MP (@lem5243046 x' s) (@lem5242956 x x' a s b h1)). Qed.
Lemma lem5243051 (a : real) (s : real -> Prop) (h1 : term359 a s) : term359 a s.
Proof. exact (h1). Qed.
Lemma lem5243069 (a : real) (s : real -> Prop) (x : real) (b : real) : (term58 s a x b) = (term129 a s x b).
Proof. exact (@lem19490 (real_le a x) (term130 x s) (real_le x b)). Qed.
Lemma lem5243070 (a : real) (s : real -> Prop) (b : real) : (term60 s a b) = (term131 a s b).
Proof. exact (fun_ext (fun x : real => @lem5243069 a s x b)). Qed.
Lemma lem5243071 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5243073 (a : real) (s : real -> Prop) (b : real) : (term61 s a b) = (term132 a s b).
Proof. exact (MK_COMB (@lem5243071) (@lem5243070 a s b)). Qed.
Lemma lem5243074 (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term132 a s b.
Proof. exact (EQ_MP (@lem5243073 a s b) (@lem5242828 s a b h1)). Qed.
Lemma lem5243088 (y : real) (x : real) (z : real) : (term349 y x z) = (term349 y x z).
Proof. exact (eq_refl (term349 y x z)). Qed.
Lemma lem5243089 (y : real) (x : real) : (term350 y x) = (term350 y x).
Proof. exact (fun_ext (fun z : real => @lem5243088 y x z)). Qed.
Lemma lem5243090 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5243091 (y : real) (x : real) : (term351 y x) = (term351 y x).
Proof. exact (MK_COMB (@lem5243090) (@lem5243089 y x)). Qed.
Lemma lem5243092 (x : real) : (term352 x) = (term352 x).
Proof. exact (fun_ext (fun y : real => @lem5243091 y x)). Qed.
Lemma lem5243093 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5243094 (x : real) : (term353 x) = (term353 x).
Proof. exact (MK_COMB (@lem5243093) (@lem5243092 x)). Qed.
Lemma lem5243095 : term354 = term354.
Proof. exact (fun_ext (fun x : real => @lem5243094 x)). Qed.
Lemma lem5243096 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5243098 : term355 = term355.
Proof. exact (MK_COMB (@lem5243096) (@lem5243095)). Qed.
Lemma lem5243099 (h1 : term175) : term355.
Proof. exact (EQ_MP (@lem5243098) (@lem5242863 h1)). Qed.
Lemma lem5243111 (s : real -> Prop) (x : real) : (term211 s x) = (term211 s x).
Proof. exact (eq_refl (term211 s x)). Qed.
Lemma lem5243112 (s : real -> Prop) : (term213 s) = (term213 s).
Proof. exact (fun_ext (fun x : real => @lem5243111 s x)). Qed.
Lemma lem5243113 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5243115 (s : real -> Prop) : (term214 s) = (term214 s).
Proof. exact (MK_COMB (@lem5243113) (@lem5243112 s)). Qed.
Lemma lem5243116 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term214 s.
Proof. exact (EQ_MP (@lem5243115 s) (@lem5242957 x x' a s b h1)). Qed.
Lemma lem5243143 (s : real -> Prop) (b : real) (h1 : term360 s b) : term360 s b.
Proof. exact (h1). Qed.
Lemma lem5243144 (_68713 : real) (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term133 a s b _68713.
Proof. exact (@lem5242982 s a b h1 _68713). Qed.
Lemma lem5243145 (a : real) (s : real -> Prop) (_68713 : real) (b : real) : (term133 a s b _68713) = (term129 a s _68713 b).
Proof. exact (eq_refl (term133 a s b _68713)). Qed.
Lemma lem5243146 (_68713 : real) (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term129 a s _68713 b.
Proof. exact (EQ_MP (@lem5243145 a s _68713 b) (@lem5243144 _68713 s a b h1)). Qed.
Lemma lem5243159 (_68718 : real) (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term361 x' s _68718.
Proof. exact (@lem5243047 x x' a s b h1 _68718). Qed.
Lemma lem5243160 (x' : real -> real) (_68718 : real) (s : real -> Prop) : (term361 x' s _68718) = (term356 x' _68718 s).
Proof. exact (eq_refl (term361 x' s _68718)). Qed.
Lemma lem5243161 (_68718 : real) (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term356 x' _68718 s.
Proof. exact (EQ_MP (@lem5243160 x' _68718 s) (@lem5243159 _68718 x x' a s b h1)). Qed.
Lemma lem5243162 (_68719 : real) (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term133 a s b _68719.
Proof. exact (@lem5243074 s a b h1 _68719). Qed.
Lemma lem5243163 (a : real) (s : real -> Prop) (_68719 : real) (b : real) : (term133 a s b _68719) = (term129 a s _68719 b).
Proof. exact (eq_refl (term133 a s b _68719)). Qed.
Lemma lem5243164 (_68719 : real) (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term129 a s _68719 b.
Proof. exact (EQ_MP (@lem5243163 a s _68719 b) (@lem5243162 _68719 s a b h1)). Qed.
Lemma lem5243165 (_68720 : real) (h1 : term175) : term362 _68720.
Proof. exact (@lem5243099 h1 _68720). Qed.
Lemma lem5243166 (_68720 : real) : (term362 _68720) = (term353 _68720).
Proof. exact (eq_refl (term362 _68720)). Qed.
Lemma lem5243167 (_68720 : real) (h1 : term175) : term353 _68720.
Proof. exact (EQ_MP (@lem5243166 _68720) (@lem5243165 _68720 h1)). Qed.
Lemma lem5243168 (_68720 : real) (_68721 : real) (h1 : term175) : term363 _68720 _68721.
Proof. exact (@lem5243167 _68720 h1 _68721). Qed.
Lemma lem5243169 (_68721 : real) (_68720 : real) : (term363 _68720 _68721) = (term351 _68721 _68720).
Proof. exact (eq_refl (term363 _68720 _68721)). Qed.
Lemma lem5243170 (_68721 : real) (_68720 : real) (h1 : term175) : term351 _68721 _68720.
Proof. exact (EQ_MP (@lem5243169 _68721 _68720) (@lem5243168 _68720 _68721 h1)). Qed.
Lemma lem5243171 (_68721 : real) (_68720 : real) (_68722 : real) (h1 : term175) : term364 _68721 _68720 _68722.
Proof. exact (@lem5243170 _68721 _68720 h1 _68722). Qed.
Lemma lem5243172 (_68721 : real) (_68720 : real) (_68722 : real) : (term364 _68721 _68720 _68722) = (term349 _68721 _68720 _68722).
Proof. exact (eq_refl (term364 _68721 _68720 _68722)). Qed.
Lemma lem5243173 (_68721 : real) (_68720 : real) (_68722 : real) (h1 : term175) : term349 _68721 _68720 _68722.
Proof. exact (EQ_MP (@lem5243172 _68721 _68720 _68722) (@lem5243171 _68721 _68720 _68722 h1)). Qed.
Lemma lem5243174 (_68723 : real) (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term365 s _68723.
Proof. exact (@lem5243116 x x' a s b h1 _68723). Qed.
Lemma lem5243175 (s : real -> Prop) (_68723 : real) : (term365 s _68723) = (term211 s _68723).
Proof. exact (eq_refl (term365 s _68723)). Qed.
Lemma lem5243209 (a : real) (s : real -> Prop) (h1 : term359 a s) : term359 a s.
Proof. exact (h1). Qed.
Lemma lem5243215 (_68718 : real) (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term366 x' _68718 s.
Proof. exact (proj1 (@lem5243161 _68718 x x' a s b h1)). Qed.
Lemma lem5243221 (_68718 : real) (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term367 x' _68718 s.
Proof. exact (proj2 (@lem5243161 _68718 x x' a s b h1)). Qed.
Lemma lem5243227 (_68713 : real) (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term136 s a _68713.
Proof. exact (proj1 (@lem5243146 _68713 s a b h1)). Qed.
Lemma lem5243244 (_68721 : real) (_68720 : real) (_68722 : real) : (term349 _68721 _68720 _68722) = (term368 _68721 _68720 _68722).
Proof. exact (@lem5241010 (term369 _68720 _68721) (term369 _68721 _68722) (real_le _68720 _68722)). Qed.
Lemma lem5243245 (_68721 : real) (_68720 : real) (_68722 : real) (h1 : term175) : term368 _68721 _68720 _68722.
Proof. exact (EQ_MP (@lem5243244 _68721 _68720 _68722) (@lem5243173 _68721 _68720 _68722 h1)). Qed.
Lemma lem5243253 (_68723 : real) (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term211 s _68723.
Proof. exact (EQ_MP (@lem5243175 s _68723) (@lem5243174 _68723 x x' a s b h1)). Qed.
Lemma lem5243255 (s : real -> Prop) (b : real) (h1 : term360 s b) : term360 s b.
Proof. exact (h1). Qed.
Lemma lem5243279 (_68719 : real) (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term370 s _68719 b.
Proof. exact (proj2 (@lem5243164 _68719 s a b h1)). Qed.
Lemma lem5243282 (a : real) (s : real -> Prop) (h1 : term359 a s) : term359 a s.
Proof. exact (h1). Qed.
Lemma lem5243283 (a : real) (s : real -> Prop) (h1 : term359 a s) : term371 a s.
Proof. exact (fun h0 : term198 a s => @lem5243282 a s h1). Qed.
Lemma lem5243285 (p : Prop) : (term372 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5243286 (a : real) (s : real -> Prop) : (term371 a s) = (term359 a s).
Proof. exact (@lem5243285 (term198 a s)). Qed.
Lemma lem5243287 (a : real) (s : real -> Prop) (h1 : term359 a s) : term359 a s.
Proof. exact (EQ_MP (@lem5243286 a s) (@lem5243283 a s h1)). Qed.
Lemma lem5243289 (b : Prop) (a : Prop) : (a \/ b) = (term153 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5243292 (x' : real -> real) (_68718 : real) (s : real -> Prop) : (term366 x' _68718 s) = (term373 x' _68718 s).
Proof. exact (@lem5243289 (term198 _68718 s) (term147 x' _68718 s)). Qed.
Lemma lem5243295 (_68718 : real) (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term373 x' _68718 s.
Proof. exact (EQ_MP (@lem5243292 x' _68718 s) (@lem5243215 _68718 x x' a s b h1)). Qed.
Lemma lem5243296 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term373 x' a s.
Proof. exact (@lem5243295 a x x' a s b h1). Qed.
Lemma lem5243299 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term359 a s) (h2 : term338 x x' a s b) : term147 x' a s.
Proof. exact (@lem5243296 x x' a s b h2 (@lem5243287 a s h1)). Qed.
Lemma lem5243300 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term359 a s) (h2 : term338 x x' a s b) : term148 x' a s.
Proof. exact (fun h0 : term149 x' a s => @lem5243299 x x' a s b h1 h2). Qed.
Lemma lem5243302 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5243303 (x' : real -> real) (a : real) (s : real -> Prop) : (term148 x' a s) = (term147 x' a s).
Proof. exact (@lem5243302 (term147 x' a s)). Qed.
Lemma lem5243304 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term359 a s) (h2 : term338 x x' a s b) : term147 x' a s.
Proof. exact (EQ_MP (@lem5243303 x' a s) (@lem5243300 x x' a s b h1 h2)). Qed.
Lemma lem5243310 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5243311 (a : real) (_68713 : real) (s : real -> Prop) : (term136 s a _68713) = (term150 a _68713 s).
Proof. exact (@lem5243310 (real_le a _68713) (term130 _68713 s)). Qed.
Lemma lem5243317 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5243318 (a : real) (_68713 : real) (s : real -> Prop) : (term151 s a _68713) = (term152 a _68713 s).
Proof. exact (MK_COMB (@lem5243317) (@lem5243311 a _68713 s)). Qed.
Lemma lem5243324 (a : real) (_68713 : real) (s : real -> Prop) : (term150 a _68713 s) = (term150 a _68713 s).
Proof. exact (eq_refl (term150 a _68713 s)). Qed.
Lemma lem5243325 (a : real) (_68713 : real) (s : real -> Prop) : ((term136 s a _68713) = (term150 a _68713 s)) = ((term150 a _68713 s) = (term150 a _68713 s)).
Proof. exact (MK_COMB (@lem5243318 a _68713 s) (@lem5243324 a _68713 s)). Qed.
Lemma lem5243327 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5243328 (x : Prop) : (x = x) = True.
Proof. exact (@lem5243327 Prop x). Qed.
Lemma lem5243329 (a : real) (_68713 : real) (s : real -> Prop) : ((term150 a _68713 s) = (term150 a _68713 s)) = True.
Proof. exact (@lem5243328 (term150 a _68713 s)). Qed.
Lemma lem5243330 (a : real) (_68713 : real) (s : real -> Prop) : ((term136 s a _68713) = (term150 a _68713 s)) = True.
Proof. exact (TRANS (@lem5243325 a _68713 s) (@lem5243329 a _68713 s)). Qed.
Lemma lem5243331 (a : real) (_68713 : real) (s : real -> Prop) : True = ((term136 s a _68713) = (term150 a _68713 s)).
Proof. exact (SYM (@lem5243330 a _68713 s)). Qed.
Lemma lem5243332 (a : real) (_68713 : real) (s : real -> Prop) : (term136 s a _68713) = (term150 a _68713 s).
Proof. exact (EQ_MP (@lem5243331 a _68713 s) (@lem0)). Qed.
Lemma lem5243333 (_68713 : real) (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term150 a _68713 s.
Proof. exact (EQ_MP (@lem5243332 a _68713 s) (@lem5243227 _68713 s a b h1)). Qed.
Lemma lem5243335 (b : Prop) (a : Prop) : (a \/ b) = (term153 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5243336 (s : real -> Prop) (a : real) (_68713 : real) : (term150 a _68713 s) = (term154 s a _68713).
Proof. exact (@lem5243335 (term130 _68713 s) (real_le a _68713)). Qed.
Lemma lem5243338 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5243339 (_68713 : real) (s : real -> Prop) : (term155 _68713 s) = (@IN real _68713 s).
Proof. exact (@lem5243338 (@IN real _68713 s)). Qed.
Lemma lem5243340 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5243341 (_68713 : real) (s : real -> Prop) : (term156 _68713 s) = (term157 _68713 s).
Proof. exact (MK_COMB (@lem5243340) (@lem5243339 _68713 s)). Qed.
Lemma lem5243342 (a : real) (_68713 : real) : (real_le a _68713) = (real_le a _68713).
Proof. exact (eq_refl (real_le a _68713)). Qed.
Lemma lem5243343 (s : real -> Prop) (a : real) (_68713 : real) : (term154 s a _68713) = (term50 s a _68713).
Proof. exact (MK_COMB (@lem5243341 _68713 s) (@lem5243342 a _68713)). Qed.
Lemma lem5243344 (s : real -> Prop) (a : real) (_68713 : real) : (term150 a _68713 s) = (term50 s a _68713).
Proof. exact (TRANS (@lem5243336 s a _68713) (@lem5243343 s a _68713)). Qed.
Lemma lem5243347 (_68713 : real) (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term50 s a _68713.
Proof. exact (EQ_MP (@lem5243344 s a _68713) (@lem5243333 _68713 s a b h1)). Qed.
Lemma lem5243348 (x' : real -> real) (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term158 s x' a.
Proof. exact (@lem5243347 (x' a) s a b h1). Qed.
Lemma lem5243351 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term359 a s) (h3 : term338 x x' a s b) : term159 x' a.
Proof. exact (@lem5243348 x' s a b h1 (@lem5243304 x x' a s b h2 h3)). Qed.
Lemma lem5243352 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term359 a s) (h3 : term338 x x' a s b) : term160 x' a.
Proof. exact (fun h0 : term135 x' a => @lem5243351 x x' a s b h1 h2 h3). Qed.
Lemma lem5243354 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5243355 (x' : real -> real) (a : real) : (term160 x' a) = (term159 x' a).
Proof. exact (@lem5243354 (term159 x' a)). Qed.
Lemma lem5243356 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term359 a s) (h3 : term338 x x' a s b) : term159 x' a.
Proof. exact (EQ_MP (@lem5243355 x' a) (@lem5243352 x x' a s b h1 h2 h3)). Qed.
Lemma lem5243362 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5243363 (s : real -> Prop) (x' : real -> real) (_68718 : real) : (term367 x' _68718 s) = (term374 s x' _68718).
Proof. exact (@lem5243362 (term198 _68718 s) (term135 x' _68718)). Qed.
Lemma lem5243369 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5243370 (s : real -> Prop) (x' : real -> real) (_68718 : real) : (term375 x' _68718 s) = (term376 s x' _68718).
Proof. exact (MK_COMB (@lem5243369) (@lem5243363 s x' _68718)). Qed.
Lemma lem5243376 (s : real -> Prop) (x' : real -> real) (_68718 : real) : (term374 s x' _68718) = (term374 s x' _68718).
Proof. exact (eq_refl (term374 s x' _68718)). Qed.
Lemma lem5243377 (s : real -> Prop) (x' : real -> real) (_68718 : real) : ((term367 x' _68718 s) = (term374 s x' _68718)) = ((term374 s x' _68718) = (term374 s x' _68718)).
Proof. exact (MK_COMB (@lem5243370 s x' _68718) (@lem5243376 s x' _68718)). Qed.
Lemma lem5243379 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5243380 (x : Prop) : (x = x) = True.
Proof. exact (@lem5243379 Prop x). Qed.
Lemma lem5243381 (s : real -> Prop) (x' : real -> real) (_68718 : real) : ((term374 s x' _68718) = (term374 s x' _68718)) = True.
Proof. exact (@lem5243380 (term374 s x' _68718)). Qed.
Lemma lem5243382 (s : real -> Prop) (x' : real -> real) (_68718 : real) : ((term367 x' _68718 s) = (term374 s x' _68718)) = True.
Proof. exact (TRANS (@lem5243377 s x' _68718) (@lem5243381 s x' _68718)). Qed.
Lemma lem5243383 (s : real -> Prop) (x' : real -> real) (_68718 : real) : True = ((term367 x' _68718 s) = (term374 s x' _68718)).
Proof. exact (SYM (@lem5243382 s x' _68718)). Qed.
Lemma lem5243384 (s : real -> Prop) (x' : real -> real) (_68718 : real) : (term367 x' _68718 s) = (term374 s x' _68718).
Proof. exact (EQ_MP (@lem5243383 s x' _68718) (@lem0)). Qed.
Lemma lem5243385 (_68718 : real) (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term374 s x' _68718.
Proof. exact (EQ_MP (@lem5243384 s x' _68718) (@lem5243221 _68718 x x' a s b h1)). Qed.
Lemma lem5243387 (b : Prop) (a : Prop) : (a \/ b) = (term153 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5243388 (x' : real -> real) (_68718 : real) (s : real -> Prop) : (term374 s x' _68718) = (term377 x' _68718 s).
Proof. exact (@lem5243387 (term135 x' _68718) (term198 _68718 s)). Qed.
Lemma lem5243390 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5243391 (x' : real -> real) (_68718 : real) : (term378 x' _68718) = (term159 x' _68718).
Proof. exact (@lem5243390 (term159 x' _68718)). Qed.
Lemma lem5243392 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5243393 (x' : real -> real) (_68718 : real) : (term379 x' _68718) = (term380 x' _68718).
Proof. exact (MK_COMB (@lem5243392) (@lem5243391 x' _68718)). Qed.
Lemma lem5243394 (_68718 : real) (s : real -> Prop) : (term198 _68718 s) = (term198 _68718 s).
Proof. exact (eq_refl (term198 _68718 s)). Qed.
Lemma lem5243395 (x' : real -> real) (_68718 : real) (s : real -> Prop) : (term377 x' _68718 s) = (term381 x' _68718 s).
Proof. exact (MK_COMB (@lem5243393 x' _68718) (@lem5243394 _68718 s)). Qed.
Lemma lem5243396 (x' : real -> real) (_68718 : real) (s : real -> Prop) : (term374 s x' _68718) = (term381 x' _68718 s).
Proof. exact (TRANS (@lem5243388 x' _68718 s) (@lem5243395 x' _68718 s)). Qed.
Lemma lem5243399 (_68718 : real) (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term381 x' _68718 s.
Proof. exact (EQ_MP (@lem5243396 x' _68718 s) (@lem5243385 _68718 x x' a s b h1)). Qed.
Lemma lem5243400 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term381 x' a s.
Proof. exact (@lem5243399 a x x' a s b h1). Qed.
Lemma lem5243403 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term359 a s) (h3 : term338 x x' a s b) : term198 a s.
Proof. exact (@lem5243400 x x' a s b h3 (@lem5243356 x x' a s b h1 h2 h3)). Qed.
Lemma lem5243404 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term338 x x' a s b) : term382 a s.
Proof. exact (fun h0 : term359 a s => @lem5243403 x x' a s b h1 h0 h2). Qed.
Lemma lem5243406 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5243407 (a : real) (s : real -> Prop) : (term382 a s) = (term198 a s).
Proof. exact (@lem5243406 (term198 a s)). Qed.
Lemma lem5243408 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term338 x x' a s b) : term198 a s.
Proof. exact (EQ_MP (@lem5243407 a s) (@lem5243404 x x' a s b h1 h2)). Qed.
Lemma lem5243411 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5243413 (a : real) (s : real -> Prop) : (term359 a s) = (term383 a s).
Proof. exact (@lem5243411 (term198 a s)). Qed.
Lemma lem5243416 (a : real) (s : real -> Prop) (h1 : term359 a s) : term383 a s.
Proof. exact (EQ_MP (@lem5243413 a s) (@lem5243209 a s h1)). Qed.
Lemma lem5243419 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term359 a s) (h3 : term338 x x' a s b) : False.
Proof. exact (@lem5243416 a s h2 (@lem5243408 x x' a s b h1 h3)). Qed.
Lemma lem5243420 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term359 a s) (h3 : term338 x x' a s b) : term146.
Proof. exact (fun h0 : ~ False => @lem5243419 x x' a s b h1 h2 h3). Qed.
Lemma lem5243422 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5243423 : term146 = False.
Proof. exact (@lem5243422 False). Qed.
Lemma lem5243424 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term359 a s) (h3 : term338 x x' a s b) : False.
Proof. exact (EQ_MP (@lem5243423) (@lem5243420 x x' a s b h1 h2 h3)). Qed.
Lemma lem5243426 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : @IN real x s.
Proof. exact (proj1 (@lem5242951 x x' a s b h1)). Qed.
Lemma lem5243427 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term384 x s.
Proof. exact (fun h0 : term130 x s => @lem5243426 x x' a s b h1). Qed.
Lemma lem5243429 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5243430 (x : real) (s : real -> Prop) : (term384 x s) = (@IN real x s).
Proof. exact (@lem5243429 (@IN real x s)). Qed.
Lemma lem5243431 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : @IN real x s.
Proof. exact (EQ_MP (@lem5243430 x s) (@lem5243427 x x' a s b h1)). Qed.
Lemma lem5243437 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5243438 (_68723 : real) (s : real -> Prop) : (term211 s _68723) = (term385 _68723 s).
Proof. exact (@lem5243437 (term212 s _68723) (term130 _68723 s)). Qed.
Lemma lem5243444 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5243445 (_68723 : real) (s : real -> Prop) : (term386 s _68723) = (term387 _68723 s).
Proof. exact (MK_COMB (@lem5243444) (@lem5243438 _68723 s)). Qed.
Lemma lem5243451 (_68723 : real) (s : real -> Prop) : (term385 _68723 s) = (term385 _68723 s).
Proof. exact (eq_refl (term385 _68723 s)). Qed.
Lemma lem5243452 (_68723 : real) (s : real -> Prop) : ((term211 s _68723) = (term385 _68723 s)) = ((term385 _68723 s) = (term385 _68723 s)).
Proof. exact (MK_COMB (@lem5243445 _68723 s) (@lem5243451 _68723 s)). Qed.
Lemma lem5243454 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5243455 (x : Prop) : (x = x) = True.
Proof. exact (@lem5243454 Prop x). Qed.
Lemma lem5243456 (_68723 : real) (s : real -> Prop) : ((term385 _68723 s) = (term385 _68723 s)) = True.
Proof. exact (@lem5243455 (term385 _68723 s)). Qed.
Lemma lem5243457 (_68723 : real) (s : real -> Prop) : ((term211 s _68723) = (term385 _68723 s)) = True.
Proof. exact (TRANS (@lem5243452 _68723 s) (@lem5243456 _68723 s)). Qed.
Lemma lem5243458 (_68723 : real) (s : real -> Prop) : True = ((term211 s _68723) = (term385 _68723 s)).
Proof. exact (SYM (@lem5243457 _68723 s)). Qed.
Lemma lem5243459 (_68723 : real) (s : real -> Prop) : (term211 s _68723) = (term385 _68723 s).
Proof. exact (EQ_MP (@lem5243458 _68723 s) (@lem0)). Qed.
Lemma lem5243460 (_68723 : real) (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term385 _68723 s.
Proof. exact (EQ_MP (@lem5243459 _68723 s) (@lem5243253 _68723 x x' a s b h1)). Qed.
Lemma lem5243462 (b : Prop) (a : Prop) : (a \/ b) = (term153 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5243463 (s : real -> Prop) (_68723 : real) : (term385 _68723 s) = (term388 s _68723).
Proof. exact (@lem5243462 (term130 _68723 s) (term212 s _68723)). Qed.
Lemma lem5243465 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5243466 (_68723 : real) (s : real -> Prop) : (term155 _68723 s) = (@IN real _68723 s).
Proof. exact (@lem5243465 (@IN real _68723 s)). Qed.
Lemma lem5243467 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5243468 (_68723 : real) (s : real -> Prop) : (term156 _68723 s) = (term157 _68723 s).
Proof. exact (MK_COMB (@lem5243467) (@lem5243466 _68723 s)). Qed.
Lemma lem5243469 (s : real -> Prop) (_68723 : real) : (term212 s _68723) = (term212 s _68723).
Proof. exact (eq_refl (term212 s _68723)). Qed.
Lemma lem5243470 (s : real -> Prop) (_68723 : real) : (term388 s _68723) = (term203 s _68723).
Proof. exact (MK_COMB (@lem5243468 _68723 s) (@lem5243469 s _68723)). Qed.
Lemma lem5243471 (s : real -> Prop) (_68723 : real) : (term385 _68723 s) = (term203 s _68723).
Proof. exact (TRANS (@lem5243463 s _68723) (@lem5243470 s _68723)). Qed.
Lemma lem5243474 (_68723 : real) (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term203 s _68723.
Proof. exact (EQ_MP (@lem5243471 s _68723) (@lem5243460 _68723 x x' a s b h1)). Qed.
Lemma lem5243475 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term203 s x.
Proof. exact (@lem5243474 x x x' a s b h1). Qed.
Lemma lem5243478 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term212 s x.
Proof. exact (@lem5243475 x x' a s b h1 (@lem5243431 x x' a s b h1)). Qed.
Lemma lem5243479 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term389 s x.
Proof. exact (fun h0 : term360 s x => @lem5243478 x x' a s b h1). Qed.
Lemma lem5243481 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5243482 (s : real -> Prop) (x : real) : (term389 s x) = (term212 s x).
Proof. exact (@lem5243481 (term212 s x)). Qed.
Lemma lem5243483 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term212 s x.
Proof. exact (EQ_MP (@lem5243482 s x) (@lem5243479 x x' a s b h1)). Qed.
Lemma lem5243485 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : @IN real x s.
Proof. exact (proj1 (@lem5242951 x x' a s b h1)). Qed.
Lemma lem5243486 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term384 x s.
Proof. exact (fun h0 : term130 x s => @lem5243485 x x' a s b h1). Qed.
Lemma lem5243488 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5243489 (x : real) (s : real -> Prop) : (term384 x s) = (@IN real x s).
Proof. exact (@lem5243488 (@IN real x s)). Qed.
Lemma lem5243490 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : @IN real x s.
Proof. exact (EQ_MP (@lem5243489 x s) (@lem5243486 x x' a s b h1)). Qed.
Lemma lem5243496 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5243497 (b : real) (_68719 : real) (s : real -> Prop) : (term370 s _68719 b) = (term390 b _68719 s).
Proof. exact (@lem5243496 (real_le _68719 b) (term130 _68719 s)). Qed.
Lemma lem5243503 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5243504 (b : real) (_68719 : real) (s : real -> Prop) : (term391 s _68719 b) = (term392 b _68719 s).
Proof. exact (MK_COMB (@lem5243503) (@lem5243497 b _68719 s)). Qed.
Lemma lem5243510 (b : real) (_68719 : real) (s : real -> Prop) : (term390 b _68719 s) = (term390 b _68719 s).
Proof. exact (eq_refl (term390 b _68719 s)). Qed.
Lemma lem5243511 (b : real) (_68719 : real) (s : real -> Prop) : ((term370 s _68719 b) = (term390 b _68719 s)) = ((term390 b _68719 s) = (term390 b _68719 s)).
Proof. exact (MK_COMB (@lem5243504 b _68719 s) (@lem5243510 b _68719 s)). Qed.
Lemma lem5243513 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5243514 (x : Prop) : (x = x) = True.
Proof. exact (@lem5243513 Prop x). Qed.
Lemma lem5243515 (b : real) (_68719 : real) (s : real -> Prop) : ((term390 b _68719 s) = (term390 b _68719 s)) = True.
Proof. exact (@lem5243514 (term390 b _68719 s)). Qed.
Lemma lem5243516 (b : real) (_68719 : real) (s : real -> Prop) : ((term370 s _68719 b) = (term390 b _68719 s)) = True.
Proof. exact (TRANS (@lem5243511 b _68719 s) (@lem5243515 b _68719 s)). Qed.
Lemma lem5243517 (b : real) (_68719 : real) (s : real -> Prop) : True = ((term370 s _68719 b) = (term390 b _68719 s)).
Proof. exact (SYM (@lem5243516 b _68719 s)). Qed.
Lemma lem5243518 (b : real) (_68719 : real) (s : real -> Prop) : (term370 s _68719 b) = (term390 b _68719 s).
Proof. exact (EQ_MP (@lem5243517 b _68719 s) (@lem0)). Qed.
Lemma lem5243519 (_68719 : real) (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term390 b _68719 s.
Proof. exact (EQ_MP (@lem5243518 b _68719 s) (@lem5243279 _68719 s a b h1)). Qed.
Lemma lem5243521 (b : Prop) (a : Prop) : (a \/ b) = (term153 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5243522 (s : real -> Prop) (_68719 : real) (b : real) : (term390 b _68719 s) = (term393 s _68719 b).
Proof. exact (@lem5243521 (term130 _68719 s) (real_le _68719 b)). Qed.
Lemma lem5243524 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5243525 (_68719 : real) (s : real -> Prop) : (term155 _68719 s) = (@IN real _68719 s).
Proof. exact (@lem5243524 (@IN real _68719 s)). Qed.
Lemma lem5243526 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5243527 (_68719 : real) (s : real -> Prop) : (term156 _68719 s) = (term157 _68719 s).
Proof. exact (MK_COMB (@lem5243526) (@lem5243525 _68719 s)). Qed.
Lemma lem5243528 (_68719 : real) (b : real) : (real_le _68719 b) = (real_le _68719 b).
Proof. exact (eq_refl (real_le _68719 b)). Qed.
Lemma lem5243529 (s : real -> Prop) (_68719 : real) (b : real) : (term393 s _68719 b) = (term394 s _68719 b).
Proof. exact (MK_COMB (@lem5243527 _68719 s) (@lem5243528 _68719 b)). Qed.
Lemma lem5243530 (s : real -> Prop) (_68719 : real) (b : real) : (term390 b _68719 s) = (term394 s _68719 b).
Proof. exact (TRANS (@lem5243522 s _68719 b) (@lem5243529 s _68719 b)). Qed.
Lemma lem5243533 (_68719 : real) (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term394 s _68719 b.
Proof. exact (EQ_MP (@lem5243530 s _68719 b) (@lem5243519 _68719 s a b h1)). Qed.
Lemma lem5243534 (x : real) (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term394 s x b.
Proof. exact (@lem5243533 x s a b h1). Qed.
Lemma lem5243537 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term338 x x' a s b) : real_le x b.
Proof. exact (@lem5243534 x s a b h1 (@lem5243490 x x' a s b h2)). Qed.
Lemma lem5243538 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term338 x x' a s b) : term395 x b.
Proof. exact (fun h0 : term369 x b => @lem5243537 x x' a s b h1 h2). Qed.
Lemma lem5243540 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5243541 (x : real) (b : real) : (term395 x b) = (real_le x b).
Proof. exact (@lem5243540 (real_le x b)). Qed.
Lemma lem5243542 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term338 x x' a s b) : real_le x b.
Proof. exact (EQ_MP (@lem5243541 x b) (@lem5243538 x x' a s b h1 h2)). Qed.
Lemma lem5243558 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5243559 (_68720 : real) (_68721 : real) (_68722 : real) : (term396 _68721 _68720 _68722) = (term397 _68720 _68721 _68722).
Proof. exact (@lem5243558 (real_le _68720 _68722) (term369 _68721 _68722)). Qed.
Lemma lem5243565 (_68720 : real) (_68721 : real) : (term398 _68720 _68721) = (term398 _68720 _68721).
Proof. exact (eq_refl (term398 _68720 _68721)). Qed.
Lemma lem5243566 (_68720 : real) (_68721 : real) (_68722 : real) : (term368 _68721 _68720 _68722) = (term399 _68720 _68721 _68722).
Proof. exact (MK_COMB (@lem5243565 _68720 _68721) (@lem5243559 _68720 _68721 _68722)). Qed.
Lemma lem5243570 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5243571 (_68720 : real) (_68721 : real) (_68722 : real) : (term399 _68720 _68721 _68722) = (term400 _68720 _68721 _68722).
Proof. exact (@lem5243570 (real_le _68720 _68722) (term369 _68720 _68721) (term369 _68721 _68722)). Qed.
Lemma lem5243587 (_68720 : real) (_68721 : real) (_68722 : real) : (term368 _68721 _68720 _68722) = (term400 _68720 _68721 _68722).
Proof. exact (TRANS (@lem5243566 _68720 _68721 _68722) (@lem5243571 _68720 _68721 _68722)). Qed.
Lemma lem5243588 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5243589 (_68720 : real) (_68721 : real) (_68722 : real) : (term401 _68721 _68720 _68722) = (term402 _68720 _68721 _68722).
Proof. exact (MK_COMB (@lem5243588) (@lem5243587 _68720 _68721 _68722)). Qed.
Lemma lem5243605 (_68720 : real) (_68721 : real) (_68722 : real) : (term400 _68720 _68721 _68722) = (term400 _68720 _68721 _68722).
Proof. exact (eq_refl (term400 _68720 _68721 _68722)). Qed.
Lemma lem5243606 (_68720 : real) (_68721 : real) (_68722 : real) : ((term368 _68721 _68720 _68722) = (term400 _68720 _68721 _68722)) = ((term400 _68720 _68721 _68722) = (term400 _68720 _68721 _68722)).
Proof. exact (MK_COMB (@lem5243589 _68720 _68721 _68722) (@lem5243605 _68720 _68721 _68722)). Qed.
Lemma lem5243608 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5243609 (x : Prop) : (x = x) = True.
Proof. exact (@lem5243608 Prop x). Qed.
Lemma lem5243610 (_68720 : real) (_68721 : real) (_68722 : real) : ((term400 _68720 _68721 _68722) = (term400 _68720 _68721 _68722)) = True.
Proof. exact (@lem5243609 (term400 _68720 _68721 _68722)). Qed.
Lemma lem5243611 (_68720 : real) (_68721 : real) (_68722 : real) : ((term368 _68721 _68720 _68722) = (term400 _68720 _68721 _68722)) = True.
Proof. exact (TRANS (@lem5243606 _68720 _68721 _68722) (@lem5243610 _68720 _68721 _68722)). Qed.
Lemma lem5243612 (_68720 : real) (_68721 : real) (_68722 : real) : True = ((term368 _68721 _68720 _68722) = (term400 _68720 _68721 _68722)).
Proof. exact (SYM (@lem5243611 _68720 _68721 _68722)). Qed.
Lemma lem5243613 (_68720 : real) (_68721 : real) (_68722 : real) : (term368 _68721 _68720 _68722) = (term400 _68720 _68721 _68722).
Proof. exact (EQ_MP (@lem5243612 _68720 _68721 _68722) (@lem0)). Qed.
Lemma lem5243614 (_68720 : real) (_68721 : real) (_68722 : real) (h1 : term175) : term400 _68720 _68721 _68722.
Proof. exact (EQ_MP (@lem5243613 _68720 _68721 _68722) (@lem5243245 _68721 _68720 _68722 h1)). Qed.
Lemma lem5243616 (b : Prop) (a : Prop) : (a \/ b) = (term153 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5243617 (_68721 : real) (_68720 : real) (_68722 : real) : (term400 _68720 _68721 _68722) = (term403 _68721 _68720 _68722).
Proof. exact (@lem5243616 (term345 _68720 _68721 _68722) (real_le _68720 _68722)). Qed.
Lemma lem5243619 (a : Prop) (b : Prop) : (term404 a b) = (term405 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5243620 (_68720 : real) (_68721 : real) (_68722 : real) : (term406 _68720 _68721 _68722) = (term407 _68720 _68721 _68722).
Proof. exact (@lem5243619 (term369 _68720 _68721) (term369 _68721 _68722)). Qed.
Lemma lem5243622 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5243623 (_68720 : real) (_68721 : real) : (term408 _68720 _68721) = (real_le _68720 _68721).
Proof. exact (@lem5243622 (real_le _68720 _68721)). Qed.
Lemma lem5243624 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5243625 (_68720 : real) (_68721 : real) : (term409 _68720 _68721) = (term410 _68720 _68721).
Proof. exact (MK_COMB (@lem5243624) (@lem5243623 _68720 _68721)). Qed.
Lemma lem5243627 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5243628 (_68721 : real) (_68722 : real) : (term408 _68721 _68722) = (real_le _68721 _68722).
Proof. exact (@lem5243627 (real_le _68721 _68722)). Qed.
Lemma lem5243629 (_68720 : real) (_68721 : real) (_68722 : real) : (term407 _68720 _68721 _68722) = (term59 _68720 _68721 _68722).
Proof. exact (MK_COMB (@lem5243625 _68720 _68721) (@lem5243628 _68721 _68722)). Qed.
Lemma lem5243630 (_68720 : real) (_68721 : real) (_68722 : real) : (term406 _68720 _68721 _68722) = (term59 _68720 _68721 _68722).
Proof. exact (TRANS (@lem5243620 _68720 _68721 _68722) (@lem5243629 _68720 _68721 _68722)). Qed.
Lemma lem5243631 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5243632 (_68720 : real) (_68721 : real) (_68722 : real) : (term411 _68720 _68721 _68722) = (term412 _68720 _68721 _68722).
Proof. exact (MK_COMB (@lem5243631) (@lem5243630 _68720 _68721 _68722)). Qed.
Lemma lem5243633 (_68720 : real) (_68722 : real) : (real_le _68720 _68722) = (real_le _68720 _68722).
Proof. exact (eq_refl (real_le _68720 _68722)). Qed.
Lemma lem5243634 (_68721 : real) (_68720 : real) (_68722 : real) : (term403 _68721 _68720 _68722) = (term192 _68721 _68720 _68722).
Proof. exact (MK_COMB (@lem5243632 _68720 _68721 _68722) (@lem5243633 _68720 _68722)). Qed.
Lemma lem5243635 (_68721 : real) (_68720 : real) (_68722 : real) : (term400 _68720 _68721 _68722) = (term192 _68721 _68720 _68722).
Proof. exact (TRANS (@lem5243617 _68721 _68720 _68722) (@lem5243634 _68721 _68720 _68722)). Qed.
Lemma lem5243637 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term338 x x' a s b) : term413 s x b.
Proof. exact (conj (@lem5243483 x x' a s b h2) (@lem5243542 x x' a s b h1 h2)). Qed.
Lemma lem5243639 (_68721 : real) (_68720 : real) (_68722 : real) (h1 : term175) : term192 _68721 _68720 _68722.
Proof. exact (EQ_MP (@lem5243635 _68721 _68720 _68722) (@lem5243614 _68720 _68721 _68722 h1)). Qed.
Lemma lem5243640 (x : real) (s : real -> Prop) (b : real) (h1 : term175) : term414 x s b.
Proof. exact (@lem5243639 x (inf s) b h1). Qed.
Lemma lem5243643 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term175) (h2 : term17 s a b) (h3 : term338 x x' a s b) : term212 s b.
Proof. exact (@lem5243640 x s b h1 (@lem5243637 x x' a s b h2 h3)). Qed.
Lemma lem5243644 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term175) (h2 : term17 s a b) (h3 : term338 x x' a s b) : term389 s b.
Proof. exact (fun h0 : term360 s b => @lem5243643 x x' a s b h1 h2 h3). Qed.
Lemma lem5243646 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5243647 (s : real -> Prop) (b : real) : (term389 s b) = (term212 s b).
Proof. exact (@lem5243646 (term212 s b)). Qed.
Lemma lem5243648 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term175) (h2 : term17 s a b) (h3 : term338 x x' a s b) : term212 s b.
Proof. exact (EQ_MP (@lem5243647 s b) (@lem5243644 x x' a s b h1 h2 h3)). Qed.
Lemma lem5243651 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5243653 (s : real -> Prop) (b : real) : (term360 s b) = (term415 s b).
Proof. exact (@lem5243651 (term212 s b)). Qed.
Lemma lem5243656 (s : real -> Prop) (b : real) (h1 : term360 s b) : term415 s b.
Proof. exact (EQ_MP (@lem5243653 s b) (@lem5243255 s b h1)). Qed.
Lemma lem5243659 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term175) (h2 : term17 s a b) (h3 : term360 s b) (h4 : term338 x x' a s b) : False.
Proof. exact (@lem5243656 s b h3 (@lem5243648 x x' a s b h1 h2 h4)). Qed.
Lemma lem5243660 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term175) (h2 : term17 s a b) (h3 : term360 s b) (h4 : term338 x x' a s b) : term146.
Proof. exact (fun h0 : ~ False => @lem5243659 x x' a s b h1 h2 h3 h4). Qed.
Lemma lem5243662 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5243663 : term146 = False.
Proof. exact (@lem5243662 False). Qed.
Lemma lem5243664 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term175) (h2 : term17 s a b) (h3 : term360 s b) (h4 : term338 x x' a s b) : False.
Proof. exact (EQ_MP (@lem5243663) (@lem5243660 x x' a s b h1 h2 h3 h4)). Qed.
Lemma lem5243665 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term175) (h2 : term17 s a b) (h3 : term360 s b) (h4 : term338 x x' a s b) : (term360 s b) = False.
Proof. exact (prop_ext (fun h5 : term360 s b => @lem5243664 x x' a s b h1 h2 h3 h4) (fun h5 : False => @lem5243255 s b h3)). Qed.
Lemma lem5243666 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term175) (h2 : term17 s a b) (h3 : term360 s b) (h4 : term338 x x' a s b) : False.
Proof. exact (EQ_MP (@lem5243665 x x' a s b h1 h2 h3 h4) (@lem5243255 s b h3)). Qed.
Lemma lem5243667 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term359 a s) (h3 : term338 x x' a s b) : (term359 a s) = False.
Proof. exact (prop_ext (fun h4 : term359 a s => @lem5243424 x x' a s b h1 h2 h3) (fun h4 : False => @lem5243209 a s h2)). Qed.
Lemma lem5243668 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term359 a s) (h3 : term338 x x' a s b) : False.
Proof. exact (EQ_MP (@lem5243667 x x' a s b h1 h2 h3) (@lem5243209 a s h2)). Qed.
Lemma lem5243669 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term175) (h2 : term17 s a b) (h3 : term360 s b) (h4 : term338 x x' a s b) : (term360 s b) = False.
Proof. exact (prop_ext (fun h5 : term360 s b => @lem5243666 x x' a s b h1 h2 h3 h4) (fun h5 : False => @lem5243143 s b h3)). Qed.
Lemma lem5243670 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term175) (h2 : term17 s a b) (h3 : term360 s b) (h4 : term338 x x' a s b) : False.
Proof. exact (EQ_MP (@lem5243669 x x' a s b h1 h2 h3 h4) (@lem5243143 s b h3)). Qed.
Lemma lem5243671 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term359 a s) (h3 : term338 x x' a s b) : (term359 a s) = False.
Proof. exact (prop_ext (fun h4 : term359 a s => @lem5243668 x x' a s b h1 h2 h3) (fun h4 : False => @lem5243051 a s h2)). Qed.
Lemma lem5243672 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term359 a s) (h3 : term338 x x' a s b) : False.
Proof. exact (EQ_MP (@lem5243671 x x' a s b h1 h2 h3) (@lem5243051 a s h2)). Qed.
Lemma lem5243673 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term175) (h2 : term17 s a b) (h3 : term360 s b) (h4 : term338 x x' a s b) : (term360 s b) = False.
Proof. exact (prop_ext (fun h5 : term360 s b => @lem5243670 x x' a s b h1 h2 h3 h4) (fun h5 : False => @lem5243143 s b h3)). Qed.
Lemma lem5243674 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term175) (h2 : term17 s a b) (h3 : term360 s b) (h4 : term338 x x' a s b) : False.
Proof. exact (EQ_MP (@lem5243673 x x' a s b h1 h2 h3 h4) (@lem5243143 s b h3)). Qed.
Lemma lem5243675 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term359 a s) (h3 : term338 x x' a s b) : (term359 a s) = False.
Proof. exact (prop_ext (fun h4 : term359 a s => @lem5243672 x x' a s b h1 h2 h3) (fun h4 : False => @lem5243051 a s h2)). Qed.
Lemma lem5243676 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term359 a s) (h3 : term338 x x' a s b) : False.
Proof. exact (EQ_MP (@lem5243675 x x' a s b h1 h2 h3) (@lem5243051 a s h2)). Qed.
Lemma lem5243677 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term175) (h2 : term17 s a b) (h3 : term338 x x' a s b) : False.
Proof. exact (or_elim (@lem5242954 x x' a s b h3) (fun h0 : term359 a s => @lem5243676 x x' a s b h2 h0 h3) (fun h0 : term360 s b => @lem5243674 x x' a s b h1 h2 h0 h3)). Qed.
Lemma lem5243678 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term175) (h2 : term17 s a b) (h3 : term338 x x' a s b) : (term338 x x' a s b) = False.
Proof. exact (prop_ext (fun h4 : term338 x x' a s b => @lem5243677 x x' a s b h1 h2 h3) (fun h4 : False => @lem5242951 x x' a s b h3)). Qed.
Lemma lem5243679 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term175) (h2 : term17 s a b) (h3 : term338 x x' a s b) : False.
Proof. exact (EQ_MP (@lem5243678 x x' a s b h1 h2 h3) (@lem5242951 x x' a s b h3)). Qed.
Lemma lem5243680 (x : real) (a : real) (s : real -> Prop) (b : real) (h1 : term175) (h2 : term17 s a b) (h3 : term341 x a s b) : False.
Proof. exact (ex_elim (@lem5242800 x a s b h3) (fun x' : real -> real => fun h0 : term340 x a s b x' => @lem5243679 x x' a s b h1 h2 h0)). Qed.
Lemma lem5243681 (a : real) (s : real -> Prop) (b : real) (h1 : term175) (h2 : term17 s a b) (h3 : term168 a s b) : False.
Proof. exact (ex_elim (@lem5242716 a s b h3) (fun x : real => fun h0 : term342 a s b x => @lem5243680 x a s b h1 h2 h0)). Qed.
Lemma lem5243682 (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term168 a s b) : term173.
Proof. exact (fun h0 : term175 => @lem5243681 a s b h0 h1 h2). Qed.
Lemma lem5243683 : term173 = term174.
Proof. exact (@lem69 term175). Qed.
Lemma lem5243684 (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term168 a s b) : term174.
Proof. exact (EQ_MP (@lem5243683) (@lem5243682 a s b h1 h2)). Qed.
Lemma lem5243685 (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term178 a s b.
Proof. exact (fun h0 : term168 a s b => @lem5243684 a s b h1 h0). Qed.
Lemma lem5243686 (a : real) (s : real -> Prop) (b : real) : term179 a s b.
Proof. exact (fun h0 : term17 s a b => @lem5243685 s a b h0). Qed.
Lemma lem5243691 (s : real -> Prop) (b : real) : term183 s b.
Proof. exact (fun a : real => @lem5243686 a s b). Qed.
Lemma lem5243696 (b : real) : term187 b.
Proof. exact (fun s : real -> Prop => @lem5243691 s b). Qed.
Lemma lem5243701 : term191.
Proof. exact (fun b : real => @lem5243696 b). Qed.
Lemma lem5243702 : term190.
Proof. exact (EQ_MP (@lem5242273) (@lem5243701)). Qed.
Lemma lem5243703 (b : real) : term416 b.
Proof. exact (@lem5243702 b). Qed.
Lemma lem5243704 (b : real) : (term416 b) = (term186 b).
Proof. exact (eq_refl (term416 b)). Qed.
Lemma lem5243705 (b : real) : term186 b.
Proof. exact (EQ_MP (@lem5243704 b) (@lem5243703 b)). Qed.
Lemma lem5243706 (b : real) (s : real -> Prop) : term417 b s.
Proof. exact (@lem5243705 b s). Qed.
Lemma lem5243707 (s : real -> Prop) (b : real) : (term417 b s) = (term182 s b).
Proof. exact (eq_refl (term417 b s)). Qed.
Lemma lem5243708 (s : real -> Prop) (b : real) : term182 s b.
Proof. exact (EQ_MP (@lem5243707 s b) (@lem5243706 b s)). Qed.
Lemma lem5243709 (s : real -> Prop) (b : real) (a : real) : term418 s b a.
Proof. exact (@lem5243708 s b a). Qed.
Lemma lem5243710 (a : real) (s : real -> Prop) (b : real) : (term418 s b a) = (term169 a s b).
Proof. exact (eq_refl (term418 s b a)). Qed.
Lemma lem5243711 (a : real) (s : real -> Prop) (b : real) : term169 a s b.
Proof. exact (EQ_MP (@lem5243710 a s b) (@lem5243709 s b a)). Qed.
Lemma lem5243713 (a : real) (s : real -> Prop) (b : real) : term169 a s b.
Proof. exact (@lem5241981 a s b (@lem5243711 a s b)). Qed.
Lemma lem5243714 (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term177 a s b.
Proof. exact (@lem5243713 a s b (@lem5241038 s a b h1)). Qed.
Lemma lem5243715 (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term168 a s b) : term173.
Proof. exact (@lem5243714 s a b h1 (@lem5241966 a s b h2)). Qed.
Lemma lem5243716 (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term168 a s b) : False.
Proof. exact (@lem5243715 a s b h1 h2 (@lem1339577)). Qed.
Lemma lem5243717 (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term168 a s b) : (term168 a s b) = False.
Proof. exact (prop_ext (fun h3 : term168 a s b => @lem5243716 a s b h1 h2) (fun h3 : False => @lem5241966 a s b h2)). Qed.
Lemma lem5243718 (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term168 a s b) : False.
Proof. exact (EQ_MP (@lem5243717 a s b h1 h2) (@lem5241966 a s b h2)). Qed.
Lemma lem5243719 (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term167 a s b.
Proof. exact (fun h0 : term168 a s b => @lem5243718 a s b h1 h0). Qed.
Lemma lem5243720 (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term166 a s b.
Proof. exact (EQ_MP (@lem5241965 a s b) (@lem5243719 s a b h1)). Qed.
Lemma lem5243721 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term18 s) : term208 a s b.
Proof. exact (@lem5243720 s a b h1 (@lem5241961 s h2)). Qed.
Lemma lem5243722 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term18 s) : term419 a s b.
Proof. exact (conj (@lem5241957 a b s h1 h2) (@lem5243721 a b s h1 h2)). Qed.
Lemma lem5243723 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term18 s) : term420 a s b.
Proof. exact (@lem5241042 a s b (@lem5243722 a b s h1 h2)). Qed.
Lemma lem5243724 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term18 s) : term23 a s b.
Proof. exact (@lem5243723 a b s h1 h2 (@lem5241036 s)). Qed.
Lemma lem5243725 (s : real -> Prop) (a : real) (b : real) (h1 : term16 s a b) : term17 s a b.
Proof. exact (proj2 (@lem5241037 s a b h1)). Qed.
Lemma lem5243726 (s : real -> Prop) (a : real) (b : real) (h1 : term16 s a b) : term18 s.
Proof. exact (proj1 (@lem5241037 s a b h1)). Qed.
Lemma lem5243727 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term18 s) : (term17 s a b) = (term23 a s b).
Proof. exact (prop_ext (fun h3 : term17 s a b => @lem5243724 a b s h1 h2) (fun h3 : term23 a s b => @lem5241038 s a b h1)). Qed.
Lemma lem5243728 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term18 s) : term23 a s b.
Proof. exact (EQ_MP (@lem5243727 a b s h1 h2) (@lem5241038 s a b h1)). Qed.
Lemma lem5243729 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term18 s) : (term18 s) = (term23 a s b).
Proof. exact (prop_ext (fun h3 : term18 s => @lem5243728 a b s h1 h2) (fun h3 : term23 a s b => @lem5241039 s h2)). Qed.
Lemma lem5243730 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term18 s) : term23 a s b.
Proof. exact (EQ_MP (@lem5243729 a b s h1 h2) (@lem5241039 s h2)). Qed.
Lemma lem5243731 (s : real -> Prop) (a : real) (b : real) (h1 : term18 s) (h2 : term16 s a b) : (term17 s a b) = (term23 a s b).
Proof. exact (prop_ext (fun h3 : term17 s a b => @lem5243730 a b s h3 h1) (fun h3 : term23 a s b => @lem5243725 s a b h2)). Qed.
Lemma lem5243732 (s : real -> Prop) (a : real) (b : real) (h1 : term18 s) (h2 : term16 s a b) : term23 a s b.
Proof. exact (EQ_MP (@lem5243731 s a b h1 h2) (@lem5243725 s a b h2)). Qed.
Lemma lem5243733 (s : real -> Prop) (a : real) (b : real) (h1 : term16 s a b) : (term18 s) = (term23 a s b).
Proof. exact (prop_ext (fun h2 : term18 s => @lem5243732 s a b h2 h1) (fun h2 : term23 a s b => @lem5243726 s a b h1)). Qed.
Lemma lem5243734 (s : real -> Prop) (a : real) (b : real) (h1 : term16 s a b) : term23 a s b.
Proof. exact (EQ_MP (@lem5243733 s a b h1) (@lem5243726 s a b h1)). Qed.
Lemma lem5243735 (a : real) (s : real -> Prop) (b : real) : term421 a s b.
Proof. exact (fun h0 : term16 s a b => @lem5243734 s a b h0). Qed.
Lemma lem5243740 (a : real) (s : real -> Prop) : term422 a s.
Proof. exact (fun b : real => @lem5243735 a s b). Qed.
Lemma lem5243745 (s : real -> Prop) : term423 s.
Proof. exact (fun a : real => @lem5243740 a s). Qed.
Lemma lem5243750 : term424.
Proof. exact (fun s : real -> Prop => @lem5243745 s). Qed.
