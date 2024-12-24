Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_OF_NUM_OF_INT_term_abbrevs.
Require Import INT_FORALL_POS_spec.
Require Import num_of_int_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm18394_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm9425_spec.
Lemma lem2834003 (P : int -> Prop) (h1 : (term0 P) = (term1 P)) : (term0 P) = (term1 P).
Proof. exact (h1). Qed.
Lemma lem2834004 (P : int -> Prop) (h1 : (term0 P) = (term1 P)) : (term1 P) = (term0 P).
Proof. exact (SYM (@lem2834003 P h1)). Qed.
Lemma lem2834005 (P : int -> Prop) (h1 : (term1 P) = (term0 P)) : (term1 P) = (term0 P).
Proof. exact (h1). Qed.
Lemma lem2834006 (P : int -> Prop) (h1 : (term1 P) = (term0 P)) : (term0 P) = (term1 P).
Proof. exact (SYM (@lem2834005 P h1)). Qed.
Lemma lem2834007 (P : int -> Prop) : ((term0 P) = (term1 P)) = ((term1 P) = (term0 P)).
Proof. exact (prop_ext (fun h1 : (term0 P) = (term1 P) => @lem2834004 P h1) (fun h1 : (term1 P) = (term0 P) => @lem2834006 P h1)). Qed.
Lemma lem2834008 : term2 = term3.
Proof. exact (fun_ext (fun P : int -> Prop => @lem2834007 P)). Qed.
Lemma lem2834009 : (@all (int -> Prop)) = (@all (int -> Prop)).
Proof. exact (eq_refl (@all (int -> Prop))). Qed.
Lemma lem2834010 : term4 = term5.
Proof. exact (MK_COMB (@lem2834009) (@lem2834008)). Qed.
Lemma lem2834011 : term5.
Proof. exact (EQ_MP (@lem2834010) (@lem2315380)). Qed.
Lemma lem2834012 (x : int) : term6 x.
Proof. exact (@lem2833930 x). Qed.
Lemma lem2834013 (x : int) : (term6 x) = ((num_of_int x) = (term7 x)).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem2834015 (P : int -> Prop) : term8 P.
Proof. exact (@lem2834011 P). Qed.
Lemma lem2834016 (P : int -> Prop) : (term8 P) = ((term1 P) = (term0 P)).
Proof. exact (eq_refl (term8 P)). Qed.
Lemma lem2834019 (P : int -> Prop) : (term1 P) = (term0 P).
Proof. exact (EQ_MP (@lem2834016 P) (@lem2834015 P)). Qed.
Lemma lem2834020 : term9 = term10.
Proof. exact (@lem2834019 term11). Qed.
Lemma lem2834021 (x : int) : (term12 x) = ((term13 x) = x).
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem2834022 (x : int) : (term14 x) = (term14 x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem2834023 (x : int) : (term15 x) = (term16 x).
Proof. exact (MK_COMB (@lem2834022 x) (@lem2834021 x)). Qed.
Lemma lem2834024 : term17 = term18.
Proof. exact (fun_ext (fun x : int => @lem2834023 x)). Qed.
Lemma lem2834025 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2834026 : term9 = term19.
Proof. exact (MK_COMB (@lem2834025) (@lem2834024)). Qed.
Lemma lem2834027 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2834028 : term20 = term21.
Proof. exact (MK_COMB (@lem2834027) (@lem2834026)). Qed.
Lemma lem2834029 (n : nat) : (term22 n) = ((term23 n) = (int_of_num n)).
Proof. exact (eq_refl (term22 n)). Qed.
Lemma lem2834030 : term24 = term25.
Proof. exact (fun_ext (fun n : nat => @lem2834029 n)). Qed.
Lemma lem2834031 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2834032 : term10 = term26.
Proof. exact (MK_COMB (@lem2834031) (@lem2834030)). Qed.
Lemma lem2834033 : (term9 = term10) = (term19 = term26).
Proof. exact (MK_COMB (@lem2834028) (@lem2834032)). Qed.
Lemma lem2834034 : term19 = term26.
Proof. exact (EQ_MP (@lem2834033) (@lem2834020)). Qed.
Lemma lem2834042 (x : int) : (num_of_int x) = (term7 x).
Proof. exact (EQ_MP (@lem2834013 x) (@lem2834012 x)). Qed.
Lemma lem2834043 (n : nat) : (term27 n) = (term28 n).
Proof. exact (@lem2834042 (int_of_num n)). Qed.
Lemma lem2834048 : int_of_num = int_of_num.
Proof. exact (eq_refl int_of_num). Qed.
Lemma lem2834049 (n : nat) : (term23 n) = (term29 n).
Proof. exact (MK_COMB (@lem2834048) (@lem2834043 n)). Qed.
Lemma lem2834050 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2834051 (n : nat) : (term30 n) = (term31 n).
Proof. exact (MK_COMB (@lem2834050) (@lem2834049 n)). Qed.
Lemma lem2834052 (n : nat) : (int_of_num n) = (int_of_num n).
Proof. exact (eq_refl (int_of_num n)). Qed.
Lemma lem2834053 (n : nat) : ((term23 n) = (int_of_num n)) = ((term29 n) = (int_of_num n)).
Proof. exact (MK_COMB (@lem2834051 n) (@lem2834052 n)). Qed.
Lemma lem2834056 : term25 = term32.
Proof. exact (fun_ext (fun n : nat => @lem2834053 n)). Qed.
Lemma lem2834057 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2834058 : term26 = term33.
Proof. exact (MK_COMB (@lem2834057) (@lem2834056)). Qed.
Lemma lem2834063 : term19 = term33.
Proof. exact (TRANS (@lem2834034) (@lem2834058)). Qed.
Lemma lem2834064 : term33 = term19.
Proof. exact (SYM (@lem2834063)). Qed.
Lemma lem2834065 (P : nat -> Prop) : (term34 P) = (ex P).
Proof. exact (@lem9425 nat P). Qed.
Lemma lem2834066 (n : nat) : (term35 n) = (term36 n).
Proof. exact (@lem2834065 (term37 n)). Qed.
Lemma lem2834067 (n : nat) : (term35 n) = ((term29 n) = (int_of_num n)).
Proof. exact (eq_refl (term35 n)). Qed.
Lemma lem2834068 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2834069 (n : nat) : (term38 n) = (term39 n).
Proof. exact (MK_COMB (@lem2834068) (@lem2834067 n)). Qed.
Lemma lem2834070 (n : nat) : (term36 n) = (term36 n).
Proof. exact (eq_refl (term36 n)). Qed.
Lemma lem2834071 (n : nat) : ((term35 n) = (term36 n)) = (((term29 n) = (int_of_num n)) = (term36 n)).
Proof. exact (MK_COMB (@lem2834069 n) (@lem2834070 n)). Qed.
Lemma lem2834072 (n : nat) : ((term29 n) = (int_of_num n)) = (term36 n).
Proof. exact (EQ_MP (@lem2834071 n) (@lem2834066 n)). Qed.
Lemma lem2834073 (n : nat) : (term36 n) = ((term29 n) = (int_of_num n)).
Proof. exact (SYM (@lem2834072 n)). Qed.
Lemma lem2834075 (p : Prop) : p = (term40 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem2834076 (n : nat) : (term36 n) = (term41 n).
Proof. exact (@lem2834075 (term36 n)). Qed.
Lemma lem2834077 (n : nat) : (term41 n) = (term36 n).
Proof. exact (SYM (@lem2834076 n)). Qed.
Lemma lem2834078 (n : nat) (h1 : term42 n) : term42 n.
Proof. exact (h1). Qed.
Lemma lem2834081 (n : nat) (h1 : term41 n) : term41 n.
Proof. exact (h1). Qed.
Lemma lem2834082 (n : nat) : term43 n.
Proof. exact (fun h0 : term41 n => @lem2834081 n h0). Qed.
Lemma lem2834083 (n : nat) (h1 : term43 n) : term43 n.
Proof. exact (h1). Qed.
Lemma lem2834084 (n : nat) (h1 : term41 n) : term41 n.
Proof. exact (h1). Qed.
Lemma lem2834085 (n : nat) (h1 : term41 n) (h2 : term43 n) : term41 n.
Proof. exact (@lem2834083 n h2 (@lem2834084 n h1)). Qed.
Lemma lem2834086 (n : nat) (h1 : term41 n) : term44 n.
Proof. exact (fun h0 : term43 n => @lem2834085 n h1 h0). Qed.
Lemma lem2834087 (n : nat) (h1 : term43 n) : term43 n.
Proof. exact (h1). Qed.
Lemma lem2834088 (n : nat) (h1 : term41 n) (h2 : term43 n) : term41 n.
Proof. exact (@lem2834086 n h1 (@lem2834087 n h2)). Qed.
Lemma lem2834089 (n : nat) (h1 : term43 n) : term43 n.
Proof. exact (fun h0 : term41 n => @lem2834088 n h0 h1). Qed.
Lemma lem2834090 (n : nat) : term45 n.
Proof. exact (fun h0 : term43 n => @lem2834089 n h0). Qed.
Lemma lem2834093 (n : nat) : term43 n.
Proof. exact (@lem2834090 n (@lem2834082 n)). Qed.
Lemma lem2834099 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem2834100 (n : nat) : (term41 n) = (term46 n).
Proof. exact (@lem2834099 (term42 n)). Qed.
Lemma lem2834102 (t : Prop) : (term47 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2834103 (n : nat) : (term46 n) = (term36 n).
Proof. exact (@lem2834102 (term36 n)). Qed.
Lemma lem2834108 (n : nat) : (term41 n) = (term36 n).
Proof. exact (TRANS (@lem2834100 n) (@lem2834103 n)). Qed.
Lemma lem2834109 : term48 = term49.
Proof. exact (fun_ext (fun n : nat => @lem2834108 n)). Qed.
Lemma lem2834110 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2834119 : term50 = term51.
Proof. exact (MK_COMB (@lem2834110) (@lem2834109)). Qed.
Lemma lem2834120 (n' : nat) (n : nat) : ((int_of_num n') = (int_of_num n)) = ((int_of_num n') = (int_of_num n)).
Proof. exact (eq_refl ((int_of_num n') = (int_of_num n))). Qed.
Lemma lem2834121 (n : nat) : (term37 n) = (term37 n).
Proof. exact (fun_ext (fun n' : nat => @lem2834120 n' n)). Qed.
Lemma lem2834122 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2834123 (n : nat) : (term36 n) = (term36 n).
Proof. exact (MK_COMB (@lem2834122) (@lem2834121 n)). Qed.
Lemma lem2834124 : term49 = term49.
Proof. exact (fun_ext (fun n : nat => @lem2834123 n)). Qed.
Lemma lem2834125 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2834126 : term51 = term51.
Proof. exact (MK_COMB (@lem2834125) (@lem2834124)). Qed.
Lemma lem2834141 : term50 = term51.
Proof. exact (TRANS (@lem2834119) (@lem2834126)). Qed.
Lemma lem2834142 : term51 = term50.
Proof. exact (SYM (@lem2834141)). Qed.
Lemma lem2834144 (p : Prop) : p = (term40 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem2834145 (n : nat) : (term36 n) = (term41 n).
Proof. exact (@lem2834144 (term36 n)). Qed.
Lemma lem2834146 (n : nat) : (term41 n) = (term36 n).
Proof. exact (SYM (@lem2834145 n)). Qed.
Lemma lem2834147 (n : nat) (h1 : term42 n) : term42 n.
Proof. exact (h1). Qed.
Lemma lem2834149 (P : nat -> Prop) : (term52 P) = (term53 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem2834150 (n : nat) : (term42 n) = (term54 n).
Proof. exact (@lem2834149 (term37 n)). Qed.
Lemma lem2834151 (n' : nat) (n : nat) : (term55 n n') = ((int_of_num n') = (int_of_num n)).
Proof. exact (eq_refl (term55 n n')). Qed.
Lemma lem2834152 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2834154 (n' : nat) (n : nat) : (term56 n n') = (term57 n' n).
Proof. exact (MK_COMB (@lem2834152) (@lem2834151 n' n)). Qed.
Lemma lem2834155 (n : nat) : (term58 n) = (term59 n).
Proof. exact (fun_ext (fun n' : nat => @lem2834154 n' n)). Qed.
Lemma lem2834156 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2834157 (n : nat) : (term54 n) = (term60 n).
Proof. exact (MK_COMB (@lem2834156) (@lem2834155 n)). Qed.
Lemma lem2834166 (n : nat) : (term42 n) = (term60 n).
Proof. exact (TRANS (@lem2834150 n) (@lem2834157 n)). Qed.
Lemma lem2834167 (n : nat) (h1 : term42 n) : term60 n.
Proof. exact (EQ_MP (@lem2834166 n) (@lem2834147 n h1)). Qed.
Lemma lem2834178 (n' : nat) (n : nat) : (term57 n' n) = (term57 n' n).
Proof. exact (eq_refl (term57 n' n)). Qed.
Lemma lem2834179 (n : nat) : (term59 n) = (term59 n).
Proof. exact (fun_ext (fun n' : nat => @lem2834178 n' n)). Qed.
Lemma lem2834180 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2834181 (n : nat) : (term60 n) = (term60 n).
Proof. exact (MK_COMB (@lem2834180) (@lem2834179 n)). Qed.
Lemma lem2834182 (n : nat) (h1 : term42 n) : term60 n.
Proof. exact (EQ_MP (@lem2834181 n) (@lem2834167 n h1)). Qed.
Lemma lem2834184 (n' : nat) (n : nat) : (term57 n' n) = (term57 n' n).
Proof. exact (eq_refl (term57 n' n)). Qed.
Lemma lem2834185 (n : nat) : (term59 n) = (term59 n).
Proof. exact (fun_ext (fun n' : nat => @lem2834184 n' n)). Qed.
Lemma lem2834186 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2834188 (n : nat) : (term60 n) = (term60 n).
Proof. exact (MK_COMB (@lem2834186) (@lem2834185 n)). Qed.
Lemma lem2834189 (n : nat) (h1 : term42 n) : term60 n.
Proof. exact (EQ_MP (@lem2834188 n) (@lem2834182 n h1)). Qed.
Lemma lem2834190 (_31112 : nat) (n : nat) (h1 : term42 n) : term61 n _31112.
Proof. exact (@lem2834189 n h1 _31112). Qed.
Lemma lem2834191 (_31112 : nat) (n : nat) : (term61 n _31112) = (term57 _31112 n).
Proof. exact (eq_refl (term61 n _31112)). Qed.
Lemma lem2834194 (_31112 : nat) (n : nat) (h1 : term42 n) : term57 _31112 n.
Proof. exact (EQ_MP (@lem2834191 _31112 n) (@lem2834190 _31112 n h1)). Qed.
Lemma lem2834208 (x : int) : x = x.
Proof. exact (@lem21386 int x). Qed.
Lemma lem2834209 (n : nat) : (int_of_num n) = (int_of_num n).
Proof. exact (@lem2834208 (int_of_num n)). Qed.
Lemma lem2834210 (n : nat) : term62 n.
Proof. exact (fun h0 : term63 n => @lem2834209 n). Qed.
Lemma lem2834212 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2834213 (n : nat) : (term62 n) = ((int_of_num n) = (int_of_num n)).
Proof. exact (@lem2834212 ((int_of_num n) = (int_of_num n))). Qed.
Lemma lem2834214 (n : nat) : (int_of_num n) = (int_of_num n).
Proof. exact (EQ_MP (@lem2834213 n) (@lem2834210 n)). Qed.
Lemma lem2834217 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem2834219 (_31112 : nat) (n : nat) : (term57 _31112 n) = (term65 _31112 n).
Proof. exact (@lem2834217 ((int_of_num _31112) = (int_of_num n))). Qed.
Lemma lem2834222 (_31112 : nat) (n : nat) (h1 : term42 n) : term65 _31112 n.
Proof. exact (EQ_MP (@lem2834219 _31112 n) (@lem2834194 _31112 n h1)). Qed.
Lemma lem2834223 (n : nat) (h1 : term42 n) : term66 n.
Proof. exact (@lem2834222 n n h1). Qed.
Lemma lem2834226 (n : nat) (h1 : term42 n) : False.
Proof. exact (@lem2834223 n h1 (@lem2834214 n)). Qed.
Lemma lem2834227 (n : nat) (h1 : term42 n) : term67.
Proof. exact (fun h0 : ~ False => @lem2834226 n h1). Qed.
Lemma lem2834229 (p : Prop) : (term64 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2834230 : term67 = False.
Proof. exact (@lem2834229 False). Qed.
Lemma lem2834231 (n : nat) (h1 : term42 n) : False.
Proof. exact (EQ_MP (@lem2834230) (@lem2834227 n h1)). Qed.
Lemma lem2834232 (n : nat) (h1 : term42 n) : (term42 n) = False.
Proof. exact (prop_ext (fun h2 : term42 n => @lem2834231 n h1) (fun h2 : False => @lem2834147 n h1)). Qed.
Lemma lem2834233 (n : nat) (h1 : term42 n) : False.
Proof. exact (EQ_MP (@lem2834232 n h1) (@lem2834147 n h1)). Qed.
Lemma lem2834234 (n : nat) : term41 n.
Proof. exact (fun h0 : term42 n => @lem2834233 n h0). Qed.
Lemma lem2834235 (n : nat) : term36 n.
Proof. exact (EQ_MP (@lem2834146 n) (@lem2834234 n)). Qed.
Lemma lem2834240 : term51.
Proof. exact (fun n : nat => @lem2834235 n). Qed.
Lemma lem2834241 : term50.
Proof. exact (EQ_MP (@lem2834142) (@lem2834240)). Qed.
Lemma lem2834242 (n : nat) : term68 n.
Proof. exact (@lem2834241 n). Qed.
Lemma lem2834243 (n : nat) : (term68 n) = (term41 n).
Proof. exact (eq_refl (term68 n)). Qed.
Lemma lem2834244 (n : nat) : term41 n.
Proof. exact (EQ_MP (@lem2834243 n) (@lem2834242 n)). Qed.
Lemma lem2834246 (n : nat) : term41 n.
Proof. exact (@lem2834093 n (@lem2834244 n)). Qed.
Lemma lem2834247 (n : nat) (h1 : term42 n) : False.
Proof. exact (@lem2834246 n (@lem2834078 n h1)). Qed.
Lemma lem2834248 (n : nat) (h1 : term42 n) : (term42 n) = False.
Proof. exact (prop_ext (fun h2 : term42 n => @lem2834247 n h1) (fun h2 : False => @lem2834078 n h1)). Qed.
Lemma lem2834249 (n : nat) (h1 : term42 n) : False.
Proof. exact (EQ_MP (@lem2834248 n h1) (@lem2834078 n h1)). Qed.
Lemma lem2834250 (n : nat) : term41 n.
Proof. exact (fun h0 : term42 n => @lem2834249 n h0). Qed.
Lemma lem2834251 (n : nat) : term36 n.
Proof. exact (EQ_MP (@lem2834077 n) (@lem2834250 n)). Qed.
Lemma lem2834252 (n : nat) : (term29 n) = (int_of_num n).
Proof. exact (EQ_MP (@lem2834073 n) (@lem2834251 n)). Qed.
Lemma lem2834257 : term33.
Proof. exact (fun n : nat => @lem2834252 n). Qed.
Lemma lem2834258 : term19.
Proof. exact (EQ_MP (@lem2834064) (@lem2834257)). Qed.
