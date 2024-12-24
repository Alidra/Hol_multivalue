Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXP_EQ_1_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import MULT_EQ_1_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_SUC_spec.
Require Import thm0_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm1834_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1855_spec.
Require Import thm1856_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Require Import thm86199_spec.
Lemma lem86999 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem87000 (x : nat) : term1 x.
Proof. exact (@lem86999 (term2 x)). Qed.
Lemma lem87001 (x : nat) : (term3 x) = (((term4 x) = term5) = (term6 x)).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem87002 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem87003 (x : nat) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem87002) (@lem87001 x)). Qed.
Lemma lem87004 (x : nat) (n : nat) : (term9 x n) = (((Nat.pow x n) = term5) = (term10 x n)).
Proof. exact (eq_refl (term9 x n)). Qed.
Lemma lem87005 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem87006 (x : nat) (n : nat) : (term11 x n) = (term12 x n).
Proof. exact (MK_COMB (@lem87005) (@lem87004 x n)). Qed.
Lemma lem87007 (x : nat) (n : nat) : (term13 x n) = (((term14 x n) = term5) = (term15 x n)).
Proof. exact (eq_refl (term13 x n)). Qed.
Lemma lem87008 (x : nat) (n : nat) : (term16 x n) = (term17 x n).
Proof. exact (MK_COMB (@lem87006 x n) (@lem87007 x n)). Qed.
Lemma lem87009 (x : nat) : (term18 x) = (term19 x).
Proof. exact (fun_ext (fun n : nat => @lem87008 x n)). Qed.
Lemma lem87010 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem87011 (x : nat) : (term20 x) = (term21 x).
Proof. exact (MK_COMB (@lem87010) (@lem87009 x)). Qed.
Lemma lem87012 (x : nat) : (term22 x) = (term23 x).
Proof. exact (MK_COMB (@lem87003 x) (@lem87011 x)). Qed.
Lemma lem87013 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem87014 (x : nat) : (term24 x) = (term25 x).
Proof. exact (MK_COMB (@lem87013) (@lem87012 x)). Qed.
Lemma lem87015 (x : nat) (n : nat) : (term9 x n) = (((Nat.pow x n) = term5) = (term10 x n)).
Proof. exact (eq_refl (term9 x n)). Qed.
Lemma lem87016 (x : nat) : (term26 x) = (term2 x).
Proof. exact (fun_ext (fun n : nat => @lem87015 x n)). Qed.
Lemma lem87017 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem87018 (x : nat) : (term27 x) = (term28 x).
Proof. exact (MK_COMB (@lem87017) (@lem87016 x)). Qed.
Lemma lem87019 (x : nat) : (term1 x) = (term29 x).
Proof. exact (MK_COMB (@lem87014 x) (@lem87018 x)). Qed.
Lemma lem87020 (x : nat) : term29 x.
Proof. exact (EQ_MP (@lem87019 x) (@lem87000 x)). Qed.
Lemma lem87051 : term30.
Proof. exact (proj1 (@lem86199)). Qed.
Lemma lem87052 (m : nat) : term31 m.
Proof. exact (@lem87051 m). Qed.
Lemma lem87053 (m : nat) : (term31 m) = ((term4 m) = term5).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem87060 (m : nat) : (term4 m) = term5.
Proof. exact (EQ_MP (@lem87053 m) (@lem87052 m)). Qed.
Lemma lem87061 (x : nat) : (term4 x) = term5.
Proof. exact (@lem87060 x). Qed.
Lemma lem87062 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem87063 (x : nat) : (term32 x) = term33.
Proof. exact (MK_COMB (@lem87062) (@lem87061 x)). Qed.
Lemma lem87064 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem87065 (x : nat) : ((term4 x) = term5) = (term5 = term5).
Proof. exact (MK_COMB (@lem87063 x) (@lem87064)). Qed.
Lemma lem87067 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem87068 (x : nat) : (x = x) = True.
Proof. exact (@lem87067 nat x). Qed.
Lemma lem87069 : (term5 = term5) = True.
Proof. exact (@lem87068 term5). Qed.
Lemma lem87070 (x : nat) : ((term4 x) = term5) = True.
Proof. exact (TRANS (@lem87065 x) (@lem87069)). Qed.
Lemma lem87071 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem87072 (x : nat) : (term34 x) = (@eq Prop True).
Proof. exact (MK_COMB (@lem87071) (@lem87070 x)). Qed.
Lemma lem87078 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem87079 (x : nat) : (x = x) = True.
Proof. exact (@lem87078 nat x). Qed.
Lemma lem87080 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem87079 (NUMERAL 0)). Qed.
Lemma lem87081 (x : nat) : (term35 x) = (term35 x).
Proof. exact (eq_refl (term35 x)). Qed.
Lemma lem87082 (x : nat) : (term6 x) = (term36 x).
Proof. exact (MK_COMB (@lem87081 x) (@lem87080)). Qed.
Lemma lem87084 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem87085 (x : nat) : (term36 x) = True.
Proof. exact (@lem87084 (x = term5)). Qed.
Lemma lem87086 (x : nat) : (term6 x) = True.
Proof. exact (TRANS (@lem87082 x) (@lem87085 x)). Qed.
Lemma lem87087 (x : nat) : (((term4 x) = term5) = (term6 x)) = (True = True).
Proof. exact (MK_COMB (@lem87072 x) (@lem87086 x)). Qed.
Lemma lem87089 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem87090 : (True = True) = True.
Proof. exact (@lem87089 True). Qed.
Lemma lem87091 (x : nat) : (((term4 x) = term5) = (term6 x)) = True.
Proof. exact (TRANS (@lem87087 x) (@lem87090)). Qed.
Lemma lem87092 (x : nat) : True = (((term4 x) = term5) = (term6 x)).
Proof. exact (SYM (@lem87091 x)). Qed.
Lemma lem87093 (x : nat) : ((term4 x) = term5) = (term6 x).
Proof. exact (EQ_MP (@lem87092 x) (@lem0)). Qed.
Lemma lem87094 (n : nat) : term37 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem87095 (n : nat) : (term37 n) = (term38 n).
Proof. exact (eq_refl (term37 n)). Qed.
Lemma lem87096 (n : nat) : term38 n.
Proof. exact (EQ_MP (@lem87095 n) (@lem87094 n)). Qed.
Lemma lem87097 (n : nat) : term39 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem87110 (m : nat) : term40 m.
Proof. exact (@lem85714 m). Qed.
Lemma lem87111 (m : nat) : (term40 m) = (term41 m).
Proof. exact (eq_refl (term40 m)). Qed.
Lemma lem87112 (m : nat) : term41 m.
Proof. exact (EQ_MP (@lem87111 m) (@lem87110 m)). Qed.
Lemma lem87113 (m : nat) (n : nat) : term42 m n.
Proof. exact (@lem87112 m n). Qed.
Lemma lem87114 (m : nat) (n : nat) : (term42 m n) = (((Nat.mul m n) = term5) = (term43 m n)).
Proof. exact (eq_refl (term42 m n)). Qed.
Lemma lem87116 : term44.
Proof. exact (proj2 (@lem86199)). Qed.
Lemma lem87117 (m : nat) : term45 m.
Proof. exact (@lem87116 m). Qed.
Lemma lem87118 (m : nat) : (term45 m) = (term46 m).
Proof. exact (eq_refl (term45 m)). Qed.
Lemma lem87119 (m : nat) : term46 m.
Proof. exact (EQ_MP (@lem87118 m) (@lem87117 m)). Qed.
Lemma lem87120 (m : nat) (n : nat) : term47 m n.
Proof. exact (@lem87119 m n). Qed.
Lemma lem87121 (m : nat) (n : nat) : (term47 m n) = ((term14 m n) = (term48 m n)).
Proof. exact (eq_refl (term47 m n)). Qed.
Lemma lem87132 (m : nat) (n : nat) : (term14 m n) = (term48 m n).
Proof. exact (EQ_MP (@lem87121 m n) (@lem87120 m n)). Qed.
Lemma lem87133 (x : nat) (n : nat) : (term14 x n) = (term48 x n).
Proof. exact (@lem87132 x n). Qed.
Lemma lem87134 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem87135 (x : nat) (n : nat) : (term49 x n) = (term50 x n).
Proof. exact (MK_COMB (@lem87134) (@lem87133 x n)). Qed.
Lemma lem87136 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem87137 (x : nat) (n : nat) : ((term14 x n) = term5) = ((term48 x n) = term5).
Proof. exact (MK_COMB (@lem87135 x n) (@lem87136)). Qed.
Lemma lem87139 (m : nat) (n : nat) : ((Nat.mul m n) = term5) = (term43 m n).
Proof. exact (EQ_MP (@lem87114 m n) (@lem87113 m n)). Qed.
Lemma lem87140 (x : nat) (n : nat) : ((term48 x n) = term5) = (term51 x n).
Proof. exact (@lem87139 x (Nat.pow x n)). Qed.
Lemma lem87146 (x : nat) (n : nat) (h1 : ((Nat.pow x n) = term5) = (term10 x n)) : ((Nat.pow x n) = term5) = (term10 x n).
Proof. exact (h1). Qed.
Lemma lem87153 (x : nat) : (term52 x) = (term52 x).
Proof. exact (eq_refl (term52 x)). Qed.
Lemma lem87154 (x : nat) (n : nat) (h1 : ((Nat.pow x n) = term5) = (term10 x n)) : (term51 x n) = (term53 x n).
Proof. exact (MK_COMB (@lem87153 x) (@lem87146 x n h1)). Qed.
Lemma lem87157 (x : nat) (n : nat) (h1 : ((Nat.pow x n) = term5) = (term10 x n)) : ((term48 x n) = term5) = (term53 x n).
Proof. exact (TRANS (@lem87140 x n) (@lem87154 x n h1)). Qed.
Lemma lem87158 (x : nat) (n : nat) (h1 : ((Nat.pow x n) = term5) = (term10 x n)) : ((term14 x n) = term5) = (term53 x n).
Proof. exact (TRANS (@lem87137 x n) (@lem87157 x n h1)). Qed.
Lemma lem87159 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem87160 (x : nat) (n : nat) (h1 : ((Nat.pow x n) = term5) = (term10 x n)) : (term54 x n) = (term55 x n).
Proof. exact (MK_COMB (@lem87159) (@lem87158 x n h1)). Qed.
Lemma lem87166 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem87097 n (@lem87096 n)). Qed.
Lemma lem87167 (x : nat) : (term35 x) = (term35 x).
Proof. exact (eq_refl (term35 x)). Qed.
Lemma lem87168 (n : nat) (x : nat) : (term15 x n) = (term56 x).
Proof. exact (MK_COMB (@lem87167 x) (@lem87166 n)). Qed.
Lemma lem87170 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem87171 (x : nat) : (term56 x) = (x = term5).
Proof. exact (@lem87170 (x = term5)). Qed.
Lemma lem87174 (n : nat) (x : nat) : (term15 x n) = (x = term5).
Proof. exact (TRANS (@lem87168 n x) (@lem87171 x)). Qed.
Lemma lem87175 (x : nat) (n : nat) (h1 : ((Nat.pow x n) = term5) = (term10 x n)) : (((term14 x n) = term5) = (term15 x n)) = ((term53 x n) = (x = term5)).
Proof. exact (MK_COMB (@lem87160 x n h1) (@lem87174 n x)). Qed.
Lemma lem87178 (x : nat) (n : nat) (h1 : ((Nat.pow x n) = term5) = (term10 x n)) : ((term53 x n) = (x = term5)) = (((term14 x n) = term5) = (term15 x n)).
Proof. exact (SYM (@lem87175 x n h1)). Qed.
Lemma lem87195 (x : nat) : term57 x.
Proof. exact (@lem9851 (x = term5)). Qed.
Lemma lem87196 (x : nat) : (term57 x) = (term58 x).
Proof. exact (eq_refl (term57 x)). Qed.
Lemma lem87197 (x : nat) : term58 x.
Proof. exact (EQ_MP (@lem87196 x) (@lem87195 x)). Qed.
Lemma lem87198 (x : nat) (h1 : (x = term5) = True) : (x = term5) = True.
Proof. exact (h1). Qed.
Lemma lem87199 (x : nat) (h1 : (x = term5) = False) : (x = term5) = False.
Proof. exact (h1). Qed.
Lemma lem87216 (n : nat) : (term59 n) = (term59 n).
Proof. exact (eq_refl (term59 n)). Qed.
Lemma lem87217 (n : nat) (x : nat) (h1 : (x = term5) = True) : (term60 n x) = (term61 n).
Proof. exact (MK_COMB (@lem87216 n) (@lem87198 x h1)). Qed.
Lemma lem87218 (n : nat) : (term61 n) = ((term62 n) = True).
Proof. exact (eq_refl (term61 n)). Qed.
Lemma lem87219 (n : nat) (x : nat) : (term63 n x) = (term63 n x).
Proof. exact (eq_refl (term63 n x)). Qed.
Lemma lem87220 (x : nat) (n : nat) : ((term60 n x) = (term61 n)) = ((term60 n x) = ((term62 n) = True)).
Proof. exact (MK_COMB (@lem87219 n x) (@lem87218 n)). Qed.
Lemma lem87221 (n : nat) (x : nat) : (term60 n x) = ((term53 x n) = (x = term5)).
Proof. exact (eq_refl (term60 n x)). Qed.
Lemma lem87222 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem87223 (n : nat) (x : nat) : (term63 n x) = (term64 n x).
Proof. exact (MK_COMB (@lem87222) (@lem87221 n x)). Qed.
Lemma lem87224 (n : nat) : ((term62 n) = True) = ((term62 n) = True).
Proof. exact (eq_refl ((term62 n) = True)). Qed.
Lemma lem87225 (x : nat) (n : nat) : ((term60 n x) = ((term62 n) = True)) = (((term53 x n) = (x = term5)) = ((term62 n) = True)).
Proof. exact (MK_COMB (@lem87223 n x) (@lem87224 n)). Qed.
Lemma lem87226 (x : nat) (n : nat) : ((term60 n x) = (term61 n)) = (((term53 x n) = (x = term5)) = ((term62 n) = True)).
Proof. exact (TRANS (@lem87220 x n) (@lem87225 x n)). Qed.
Lemma lem87227 (n : nat) (x : nat) (h1 : (x = term5) = True) : ((term53 x n) = (x = term5)) = ((term62 n) = True).
Proof. exact (EQ_MP (@lem87226 x n) (@lem87217 n x h1)). Qed.
Lemma lem87228 (n : nat) (x : nat) (h1 : (x = term5) = True) : ((term62 n) = True) = ((term53 x n) = (x = term5)).
Proof. exact (SYM (@lem87227 n x h1)). Qed.
Lemma lem87229 (n : nat) : (term59 n) = (term59 n).
Proof. exact (eq_refl (term59 n)). Qed.
Lemma lem87230 (n : nat) (x : nat) (h1 : (x = term5) = False) : (term60 n x) = (term65 n).
Proof. exact (MK_COMB (@lem87229 n) (@lem87199 x h1)). Qed.
Lemma lem87231 (n : nat) : (term65 n) = ((term66 n) = False).
Proof. exact (eq_refl (term65 n)). Qed.
Lemma lem87232 (n : nat) (x : nat) : (term63 n x) = (term63 n x).
Proof. exact (eq_refl (term63 n x)). Qed.
Lemma lem87233 (x : nat) (n : nat) : ((term60 n x) = (term65 n)) = ((term60 n x) = ((term66 n) = False)).
Proof. exact (MK_COMB (@lem87232 n x) (@lem87231 n)). Qed.
Lemma lem87234 (n : nat) (x : nat) : (term60 n x) = ((term53 x n) = (x = term5)).
Proof. exact (eq_refl (term60 n x)). Qed.
Lemma lem87235 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem87236 (n : nat) (x : nat) : (term63 n x) = (term64 n x).
Proof. exact (MK_COMB (@lem87235) (@lem87234 n x)). Qed.
Lemma lem87237 (n : nat) : ((term66 n) = False) = ((term66 n) = False).
Proof. exact (eq_refl ((term66 n) = False)). Qed.
Lemma lem87238 (x : nat) (n : nat) : ((term60 n x) = ((term66 n) = False)) = (((term53 x n) = (x = term5)) = ((term66 n) = False)).
Proof. exact (MK_COMB (@lem87236 n x) (@lem87237 n)). Qed.
Lemma lem87239 (x : nat) (n : nat) : ((term60 n x) = (term65 n)) = (((term53 x n) = (x = term5)) = ((term66 n) = False)).
Proof. exact (TRANS (@lem87233 x n) (@lem87238 x n)). Qed.
Lemma lem87240 (n : nat) (x : nat) (h1 : (x = term5) = False) : ((term53 x n) = (x = term5)) = ((term66 n) = False).
Proof. exact (EQ_MP (@lem87239 x n) (@lem87230 n x h1)). Qed.
Lemma lem87241 (n : nat) (x : nat) (h1 : (x = term5) = False) : ((term66 n) = False) = ((term53 x n) = (x = term5)).
Proof. exact (SYM (@lem87240 n x h1)). Qed.
Lemma lem87243 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem87244 (n : nat) : ((term62 n) = True) = (term62 n).
Proof. exact (@lem87243 (term62 n)). Qed.
Lemma lem87246 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem87247 (n : nat) : (term62 n) = (term67 n).
Proof. exact (@lem87246 (term67 n)). Qed.
Lemma lem87249 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem87250 (n : nat) : (term67 n) = True.
Proof. exact (@lem87249 (n = (NUMERAL 0))). Qed.
Lemma lem87251 (n : nat) : (term62 n) = True.
Proof. exact (TRANS (@lem87247 n) (@lem87250 n)). Qed.
Lemma lem87252 (n : nat) : ((term62 n) = True) = True.
Proof. exact (TRANS (@lem87244 n) (@lem87251 n)). Qed.
Lemma lem87253 (n : nat) : True = ((term62 n) = True).
Proof. exact (SYM (@lem87252 n)). Qed.
Lemma lem87254 (n : nat) : (term62 n) = True.
Proof. exact (EQ_MP (@lem87253 n) (@lem0)). Qed.
Lemma lem87256 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem87257 (n : nat) : ((term66 n) = False) = (term68 n).
Proof. exact (@lem87256 (term66 n)). Qed.
Lemma lem87259 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem87260 (n : nat) : (term66 n) = False.
Proof. exact (@lem87259 (term69 n)). Qed.
Lemma lem87261 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem87262 (n : nat) : (term68 n) = (~ False).
Proof. exact (MK_COMB (@lem87261) (@lem87260 n)). Qed.
Lemma lem87264 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem87265 (n : nat) : (term68 n) = True.
Proof. exact (TRANS (@lem87262 n) (@lem87264)). Qed.
Lemma lem87266 (n : nat) : ((term66 n) = False) = True.
Proof. exact (TRANS (@lem87257 n) (@lem87265 n)). Qed.
Lemma lem87267 (n : nat) : True = ((term66 n) = False).
Proof. exact (SYM (@lem87266 n)). Qed.
Lemma lem87268 (n : nat) : (term66 n) = False.
Proof. exact (EQ_MP (@lem87267 n) (@lem0)). Qed.
Lemma lem87269 (n : nat) (x : nat) (h1 : (x = term5) = False) : (term53 x n) = (x = term5).
Proof. exact (EQ_MP (@lem87241 n x h1) (@lem87268 n)). Qed.
Lemma lem87270 (n : nat) (x : nat) (h1 : (x = term5) = True) : (term53 x n) = (x = term5).
Proof. exact (EQ_MP (@lem87228 n x h1) (@lem87254 n)). Qed.
Lemma lem87273 (n : nat) (x : nat) : (term53 x n) = (x = term5).
Proof. exact (or_elim (@lem87197 x) (fun h0 : (x = term5) = True => @lem87270 n x h0) (fun h0 : (x = term5) = False => @lem87269 n x h0)). Qed.
Lemma lem87274 (x : nat) (n : nat) (h1 : ((Nat.pow x n) = term5) = (term10 x n)) : ((term14 x n) = term5) = (term15 x n).
Proof. exact (EQ_MP (@lem87178 x n h1) (@lem87273 n x)). Qed.
Lemma lem87275 (x : nat) (n : nat) : term17 x n.
Proof. exact (fun h0 : ((Nat.pow x n) = term5) = (term10 x n) => @lem87274 x n h0). Qed.
Lemma lem87280 (x : nat) : term21 x.
Proof. exact (fun n : nat => @lem87275 x n). Qed.
Lemma lem87281 (x : nat) : term23 x.
Proof. exact (conj (@lem87093 x) (@lem87280 x)). Qed.
Lemma lem87282 (x : nat) : term28 x.
Proof. exact (@lem87020 x (@lem87281 x)). Qed.
Lemma lem87287 : term70.
Proof. exact (fun x : nat => @lem87282 x). Qed.
