Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_BOOL_THM_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import DE_MORGAN_THM_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_EXISTS_THM_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm11004_spec.
Require Import thm11005_spec.
Require Import thm1823_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem11007 {A : Type'} (P : A -> Prop) : term0 A P.
Proof. exact (@lem10660 A P). Qed.
Lemma lem11008 {A : Type'} (P : A -> Prop) : (term0 A P) = ((term1 A P) = (term2 A P)).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem11010 (t1 : Prop) : term3 t1.
Proof. exact (@lem10089 t1). Qed.
Lemma lem11011 (t1 : Prop) : (term3 t1) = (term4 t1).
Proof. exact (eq_refl (term3 t1)). Qed.
Lemma lem11012 (t1 : Prop) : term4 t1.
Proof. exact (EQ_MP (@lem11011 t1) (@lem11010 t1)). Qed.
Lemma lem11013 (t1 : Prop) (t2 : Prop) : term5 t1 t2.
Proof. exact (@lem11012 t1 t2). Qed.
Lemma lem11014 (t1 : Prop) (t2 : Prop) : (term5 t1 t2) = (term6 t1 t2).
Proof. exact (eq_refl (term5 t1 t2)). Qed.
Lemma lem11015 (t1 : Prop) (t2 : Prop) : term6 t1 t2.
Proof. exact (EQ_MP (@lem11014 t1 t2) (@lem11013 t1 t2)). Qed.
Lemma lem11028 (p : Prop) : term7 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem11029 (p : Prop) : (term7 p) = (term8 p).
Proof. exact (eq_refl (term7 p)). Qed.
Lemma lem11030 (p : Prop) : term8 p.
Proof. exact (EQ_MP (@lem11029 p) (@lem11028 p)). Qed.
Lemma lem11031 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem11032 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem11043 (q : Prop) : (term9 q) = (term9 q).
Proof. exact (eq_refl (term9 q)). Qed.
Lemma lem11044 (q : Prop) (p : Prop) (h1 : p = True) : (term10 q p) = (term11 q).
Proof. exact (MK_COMB (@lem11043 q) (@lem11031 p h1)). Qed.
Lemma lem11045 (q : Prop) : (term11 q) = (term12 q).
Proof. exact (eq_refl (term11 q)). Qed.
Lemma lem11046 (q : Prop) (p : Prop) : (term13 q p) = (term13 q p).
Proof. exact (eq_refl (term13 q p)). Qed.
Lemma lem11047 (p : Prop) (q : Prop) : ((term10 q p) = (term11 q)) = ((term10 q p) = (term12 q)).
Proof. exact (MK_COMB (@lem11046 q p) (@lem11045 q)). Qed.
Lemma lem11048 (p : Prop) (q : Prop) : (term10 q p) = (term14 p q).
Proof. exact (eq_refl (term10 q p)). Qed.
Lemma lem11049 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem11050 (p : Prop) (q : Prop) : (term13 q p) = (term15 p q).
Proof. exact (MK_COMB (@lem11049) (@lem11048 p q)). Qed.
Lemma lem11051 (q : Prop) : (term12 q) = (term12 q).
Proof. exact (eq_refl (term12 q)). Qed.
Lemma lem11052 (p : Prop) (q : Prop) : ((term10 q p) = (term12 q)) = ((term14 p q) = (term12 q)).
Proof. exact (MK_COMB (@lem11050 p q) (@lem11051 q)). Qed.
Lemma lem11053 (p : Prop) (q : Prop) : ((term10 q p) = (term11 q)) = ((term14 p q) = (term12 q)).
Proof. exact (TRANS (@lem11047 p q) (@lem11052 p q)). Qed.
Lemma lem11054 (q : Prop) (p : Prop) (h1 : p = True) : (term14 p q) = (term12 q).
Proof. exact (EQ_MP (@lem11053 p q) (@lem11044 q p h1)). Qed.
Lemma lem11055 (q : Prop) (p : Prop) (h1 : p = True) : (term12 q) = (term14 p q).
Proof. exact (SYM (@lem11054 q p h1)). Qed.
Lemma lem11056 (q : Prop) : (term9 q) = (term9 q).
Proof. exact (eq_refl (term9 q)). Qed.
Lemma lem11057 (q : Prop) (p : Prop) (h1 : p = False) : (term10 q p) = (term16 q).
Proof. exact (MK_COMB (@lem11056 q) (@lem11032 p h1)). Qed.
Lemma lem11058 (q : Prop) : (term16 q) = (term17 q).
Proof. exact (eq_refl (term16 q)). Qed.
Lemma lem11059 (q : Prop) (p : Prop) : (term13 q p) = (term13 q p).
Proof. exact (eq_refl (term13 q p)). Qed.
Lemma lem11060 (p : Prop) (q : Prop) : ((term10 q p) = (term16 q)) = ((term10 q p) = (term17 q)).
Proof. exact (MK_COMB (@lem11059 q p) (@lem11058 q)). Qed.
Lemma lem11061 (p : Prop) (q : Prop) : (term10 q p) = (term14 p q).
Proof. exact (eq_refl (term10 q p)). Qed.
Lemma lem11062 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem11063 (p : Prop) (q : Prop) : (term13 q p) = (term15 p q).
Proof. exact (MK_COMB (@lem11062) (@lem11061 p q)). Qed.
Lemma lem11064 (q : Prop) : (term17 q) = (term17 q).
Proof. exact (eq_refl (term17 q)). Qed.
Lemma lem11065 (p : Prop) (q : Prop) : ((term10 q p) = (term17 q)) = ((term14 p q) = (term17 q)).
Proof. exact (MK_COMB (@lem11063 p q) (@lem11064 q)). Qed.
Lemma lem11066 (p : Prop) (q : Prop) : ((term10 q p) = (term16 q)) = ((term14 p q) = (term17 q)).
Proof. exact (TRANS (@lem11060 p q) (@lem11065 p q)). Qed.
Lemma lem11067 (q : Prop) (p : Prop) (h1 : p = False) : (term14 p q) = (term17 q).
Proof. exact (EQ_MP (@lem11066 p q) (@lem11057 q p h1)). Qed.
Lemma lem11068 (q : Prop) (p : Prop) (h1 : p = False) : (term17 q) = (term14 p q).
Proof. exact (SYM (@lem11067 q p h1)). Qed.
Lemma lem11076 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem11077 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem11078 : term18 = (@eq Prop False).
Proof. exact (MK_COMB (@lem11077) (@lem11076)). Qed.
Lemma lem11079 (q : Prop) : (~ q) = (~ q).
Proof. exact (eq_refl (~ q)). Qed.
Lemma lem11080 (q : Prop) : ((~ True) = (~ q)) = (False = (~ q)).
Proof. exact (MK_COMB (@lem11078) (@lem11079 q)). Qed.
Lemma lem11082 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem11083 (q : Prop) : (False = (~ q)) = (term19 q).
Proof. exact (@lem11082 (~ q)). Qed.
Lemma lem11084 (q : Prop) : ((~ True) = (~ q)) = (term19 q).
Proof. exact (TRANS (@lem11080 q) (@lem11083 q)). Qed.
Lemma lem11085 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem11086 (q : Prop) : (term20 q) = (term21 q).
Proof. exact (MK_COMB (@lem11085) (@lem11084 q)). Qed.
Lemma lem11088 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem11089 (q : Prop) : (True = q) = q.
Proof. exact (@lem11088 q). Qed.
Lemma lem11090 (q : Prop) : (term12 q) = (term22 q).
Proof. exact (MK_COMB (@lem11086 q) (@lem11089 q)). Qed.
Lemma lem11093 (q : Prop) : (term22 q) = (term12 q).
Proof. exact (SYM (@lem11090 q)). Qed.
Lemma lem11102 (t : Prop) : (term19 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem11103 (q : Prop) : (term19 q) = q.
Proof. exact (@lem11102 q). Qed.
Lemma lem11104 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem11105 (q : Prop) : (term21 q) = (imp q).
Proof. exact (MK_COMB (@lem11104) (@lem11103 q)). Qed.
Lemma lem11106 (q : Prop) : q = q.
Proof. exact (eq_refl q). Qed.
Lemma lem11107 (q : Prop) : (term22 q) = (q -> q).
Proof. exact (MK_COMB (@lem11105 q) (@lem11106 q)). Qed.
Lemma lem11109 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem11110 (q : Prop) : (q -> q) = True.
Proof. exact (@lem11109 q). Qed.
Lemma lem11111 (q : Prop) : (term22 q) = True.
Proof. exact (TRANS (@lem11107 q) (@lem11110 q)). Qed.
Lemma lem11112 (q : Prop) : True = (term22 q).
Proof. exact (SYM (@lem11111 q)). Qed.
Lemma lem11113 (q : Prop) : term22 q.
Proof. exact (EQ_MP (@lem11112 q) (@lem0)). Qed.
Lemma lem11114 (q : Prop) : term12 q.
Proof. exact (EQ_MP (@lem11093 q) (@lem11113 q)). Qed.
Lemma lem11122 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem11123 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem11124 : term23 = (@eq Prop True).
Proof. exact (MK_COMB (@lem11123) (@lem11122)). Qed.
Lemma lem11125 (q : Prop) : (~ q) = (~ q).
Proof. exact (eq_refl (~ q)). Qed.
Lemma lem11126 (q : Prop) : ((~ False) = (~ q)) = (True = (~ q)).
Proof. exact (MK_COMB (@lem11124) (@lem11125 q)). Qed.
Lemma lem11128 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem11129 (q : Prop) : (True = (~ q)) = (~ q).
Proof. exact (@lem11128 (~ q)). Qed.
Lemma lem11130 (q : Prop) : ((~ False) = (~ q)) = (~ q).
Proof. exact (TRANS (@lem11126 q) (@lem11129 q)). Qed.
Lemma lem11131 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem11132 (q : Prop) : (term24 q) = (term25 q).
Proof. exact (MK_COMB (@lem11131) (@lem11130 q)). Qed.
Lemma lem11134 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem11135 (q : Prop) : (False = q) = (~ q).
Proof. exact (@lem11134 q). Qed.
Lemma lem11136 (q : Prop) : (term17 q) = (term26 q).
Proof. exact (MK_COMB (@lem11132 q) (@lem11135 q)). Qed.
Lemma lem11138 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem11139 (q : Prop) : (term26 q) = True.
Proof. exact (@lem11138 (~ q)). Qed.
Lemma lem11140 (q : Prop) : (term17 q) = True.
Proof. exact (TRANS (@lem11136 q) (@lem11139 q)). Qed.
Lemma lem11141 (q : Prop) : True = (term17 q).
Proof. exact (SYM (@lem11140 q)). Qed.
Lemma lem11142 (q : Prop) : term17 q.
Proof. exact (EQ_MP (@lem11141 q) (@lem0)). Qed.
Lemma lem11143 (q : Prop) (p : Prop) (h1 : p = False) : term14 p q.
Proof. exact (EQ_MP (@lem11068 q p h1) (@lem11142 q)). Qed.
Lemma lem11144 (q : Prop) (p : Prop) (h1 : p = True) : term14 p q.
Proof. exact (EQ_MP (@lem11055 q p h1) (@lem11114 q)). Qed.
Lemma lem11147 (p : Prop) (q : Prop) : term14 p q.
Proof. exact (or_elim (@lem11030 p) (fun h0 : p = True => @lem11144 q p h0) (fun h0 : p = False => @lem11143 q p h0)). Qed.
Lemma lem11148 (p : Prop) (q : Prop) (h1 : term14 p q) : term14 p q.
Proof. exact (h1). Qed.
Lemma lem11149 (p : Prop) (q : Prop) (h1 : (~ p) = (~ q)) : (~ p) = (~ q).
Proof. exact (h1). Qed.
Lemma lem11150 (p : Prop) (q : Prop) (h1 : (~ p) = (~ q)) (h2 : term14 p q) : p = q.
Proof. exact (@lem11148 p q h2 (@lem11149 p q h1)). Qed.
Lemma lem11151 (p : Prop) (q : Prop) (h1 : (~ p) = (~ q)) : term27 p q.
Proof. exact (fun h0 : term14 p q => @lem11150 p q h1 h0). Qed.
Lemma lem11152 (p : Prop) (q : Prop) (h1 : term14 p q) : term14 p q.
Proof. exact (h1). Qed.
Lemma lem11153 (p : Prop) (q : Prop) (h1 : (~ p) = (~ q)) (h2 : term14 p q) : p = q.
Proof. exact (@lem11151 p q h1 (@lem11152 p q h2)). Qed.
Lemma lem11154 (p : Prop) (q : Prop) (h1 : term14 p q) : term14 p q.
Proof. exact (fun h0 : (~ p) = (~ q) => @lem11153 p q h0 h1). Qed.
Lemma lem11155 (p : Prop) (q : Prop) : term28 p q.
Proof. exact (fun h0 : term14 p q => @lem11154 p q h0). Qed.
Lemma lem11158 (p : Prop) (q : Prop) : term14 p q.
Proof. exact (@lem11155 p q (@lem11147 p q)). Qed.
Lemma lem11159 (P : Prop -> Prop) : term29 P.
Proof. exact (@lem11158 (term30 P) (term31 P)). Qed.
Lemma lem11163 {A : Type'} (P : A -> Prop) : (term1 A P) = (term2 A P).
Proof. exact (EQ_MP (@lem11008 A P) (@lem11007 A P)). Qed.
Lemma lem11164 (P : Prop -> Prop) : (term32 P) = (term33 P).
Proof. exact (@lem11163 Prop P). Qed.
Lemma lem11170 (P : Prop -> Prop) : (term34 P) = (term35 P).
Proof. exact (EQ_MP (@lem11005 P) (@lem11004 P)). Qed.
Lemma lem11171 (P : Prop -> Prop) : (term36 P) = (term37 P).
Proof. exact (@lem11170 (term38 P)). Qed.
Lemma lem11172 (P : Prop -> Prop) (b : Prop) : (term39 P b) = (term40 P b).
Proof. exact (eq_refl (term39 P b)). Qed.
Lemma lem11173 (P : Prop -> Prop) : (term41 P) = (term38 P).
Proof. exact (fun_ext (fun b : Prop => @lem11172 P b)). Qed.
Lemma lem11174 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem11175 (P : Prop -> Prop) : (term36 P) = (term33 P).
Proof. exact (MK_COMB (@lem11174) (@lem11173 P)). Qed.
Lemma lem11176 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem11177 (P : Prop -> Prop) : (term42 P) = (term43 P).
Proof. exact (MK_COMB (@lem11176) (@lem11175 P)). Qed.
Lemma lem11178 (P : Prop -> Prop) : (term44 P) = (term45 P).
Proof. exact (eq_refl (term44 P)). Qed.
Lemma lem11179 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem11180 (P : Prop -> Prop) : (term46 P) = (term47 P).
Proof. exact (MK_COMB (@lem11179) (@lem11178 P)). Qed.
Lemma lem11181 (P : Prop -> Prop) : (term48 P) = (term49 P).
Proof. exact (eq_refl (term48 P)). Qed.
Lemma lem11182 (P : Prop -> Prop) : (term37 P) = (term50 P).
Proof. exact (MK_COMB (@lem11180 P) (@lem11181 P)). Qed.
Lemma lem11183 (P : Prop -> Prop) : ((term36 P) = (term37 P)) = ((term33 P) = (term50 P)).
Proof. exact (MK_COMB (@lem11177 P) (@lem11182 P)). Qed.
Lemma lem11184 (P : Prop -> Prop) : (term33 P) = (term50 P).
Proof. exact (EQ_MP (@lem11183 P) (@lem11171 P)). Qed.
Lemma lem11187 (P : Prop -> Prop) : (term32 P) = (term50 P).
Proof. exact (TRANS (@lem11164 P) (@lem11184 P)). Qed.
Lemma lem11188 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem11189 (P : Prop -> Prop) : (term51 P) = (term52 P).
Proof. exact (MK_COMB (@lem11188) (@lem11187 P)). Qed.
Lemma lem11191 (t1 : Prop) (t2 : Prop) : (term53 t1 t2) = (term54 t1 t2).
Proof. exact (proj2 (@lem11015 t1 t2)). Qed.
Lemma lem11192 (P : Prop -> Prop) : (term55 P) = (term50 P).
Proof. exact (@lem11191 (P True) (P False)). Qed.
Lemma lem11195 (P : Prop -> Prop) : ((term32 P) = (term55 P)) = ((term50 P) = (term50 P)).
Proof. exact (MK_COMB (@lem11189 P) (@lem11192 P)). Qed.
Lemma lem11197 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem11198 (x : Prop) : (x = x) = True.
Proof. exact (@lem11197 Prop x). Qed.
Lemma lem11199 (P : Prop -> Prop) : ((term50 P) = (term50 P)) = True.
Proof. exact (@lem11198 (term50 P)). Qed.
Lemma lem11200 (P : Prop -> Prop) : ((term32 P) = (term55 P)) = True.
Proof. exact (TRANS (@lem11195 P) (@lem11199 P)). Qed.
Lemma lem11201 (P : Prop -> Prop) : True = ((term32 P) = (term55 P)).
Proof. exact (SYM (@lem11200 P)). Qed.
Lemma lem11202 (P : Prop -> Prop) : (term32 P) = (term55 P).
Proof. exact (EQ_MP (@lem11201 P) (@lem0)). Qed.
Lemma lem11203 (P : Prop -> Prop) : (term30 P) = (term31 P).
Proof. exact (@lem11159 P (@lem11202 P)). Qed.
