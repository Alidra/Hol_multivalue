Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_IMAGE_term_abbrevs.
Require Import dest_int_rep_spec.
Require Import int_neg_spec.
Require Import int_of_num_spec.
Require Import int_of_num_th_spec.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm2267744_spec.
Require Import thm2267745_spec.
Lemma lem2295097 (n : nat) (h1 : (int_of_num n) = (term0 n)) : (int_of_num n) = (term0 n).
Proof. exact (h1). Qed.
Lemma lem2295098 (n : nat) (h1 : (int_of_num n) = (term0 n)) : (term0 n) = (int_of_num n).
Proof. exact (SYM (@lem2295097 n h1)). Qed.
Lemma lem2295099 (n : nat) (h1 : (term0 n) = (int_of_num n)) : (term0 n) = (int_of_num n).
Proof. exact (h1). Qed.
Lemma lem2295100 (n : nat) (h1 : (term0 n) = (int_of_num n)) : (int_of_num n) = (term0 n).
Proof. exact (SYM (@lem2295099 n h1)). Qed.
Lemma lem2295101 (n : nat) : ((int_of_num n) = (term0 n)) = ((term0 n) = (int_of_num n)).
Proof. exact (prop_ext (fun h1 : (int_of_num n) = (term0 n) => @lem2295098 n h1) (fun h1 : (term0 n) = (int_of_num n) => @lem2295100 n h1)). Qed.
Lemma lem2295102 : term1 = term2.
Proof. exact (fun_ext (fun n : nat => @lem2295101 n)). Qed.
Lemma lem2295103 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2295104 : term3 = term4.
Proof. exact (MK_COMB (@lem2295103) (@lem2295102)). Qed.
Lemma lem2295105 : term4.
Proof. exact (EQ_MP (@lem2295104) (@lem2271820)). Qed.
Lemma lem2295106 (n : nat) : term5 n.
Proof. exact (@lem2271980 n). Qed.
Lemma lem2295107 (n : nat) : (term5 n) = ((term6 n) = (real_of_num n)).
Proof. exact (eq_refl (term5 n)). Qed.
Lemma lem2295109 (n : nat) : term7 n.
Proof. exact (@lem2295105 n). Qed.
Lemma lem2295110 (n : nat) : (term7 n) = ((term0 n) = (int_of_num n)).
Proof. exact (eq_refl (term7 n)). Qed.
Lemma lem2295112 (i : int) : term8 i.
Proof. exact (@lem2272662 i). Qed.
Lemma lem2295113 (i : int) : (term8 i) = ((int_neg i) = (term9 i)).
Proof. exact (eq_refl (term8 i)). Qed.
Lemma lem2295115 (n : nat) : term10 n.
Proof. exact (@lem2271820 n). Qed.
Lemma lem2295116 (n : nat) : (term10 n) = ((int_of_num n) = (term0 n)).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem2295118 : int_of_real = int_of_real.
Proof. exact (eq_refl int_of_real). Qed.
Lemma lem2295119 (x : int) : term11 x.
Proof. exact (@lem2267790 x). Qed.
Lemma lem2295120 (x : int) : (term11 x) = (term12 x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem2295121 (x : int) : term12 x.
Proof. exact (EQ_MP (@lem2295120 x) (@lem2295119 x)). Qed.
Lemma lem2295122 (x : int) (n : nat) (h1 : term13 x n) : term13 x n.
Proof. exact (h1). Qed.
Lemma lem2295123 (x : int) (n : nat) (h1 : (real_of_int x) = (real_of_num n)) : (real_of_int x) = (real_of_num n).
Proof. exact (h1). Qed.
Lemma lem2295124 (x : int) (n : nat) (h1 : (real_of_int x) = (term14 n)) : (real_of_int x) = (term14 n).
Proof. exact (h1). Qed.
Lemma lem2295125 (x : int) (n : nat) (h1 : (real_of_int x) = (real_of_num n)) : (term15 x) = (term0 n).
Proof. exact (MK_COMB (@lem2295118) (@lem2295123 x n h1)). Qed.
Lemma lem2295126 (x : int) (n : nat) (h1 : (real_of_int x) = (term14 n)) : (term15 x) = (term16 n).
Proof. exact (MK_COMB (@lem2295118) (@lem2295124 x n h1)). Qed.
Lemma lem2295134 (a : int) : (term15 a) = a.
Proof. exact (EQ_MP (@lem2267745 a) (@lem2267744 a)). Qed.
Lemma lem2295135 (x : int) : (term15 x) = x.
Proof. exact (@lem2295134 x). Qed.
Lemma lem2295136 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2295137 (x : int) : (term17 x) = (@eq int x).
Proof. exact (MK_COMB (@lem2295136) (@lem2295135 x)). Qed.
Lemma lem2295138 (n : nat) : (term0 n) = (term0 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2295139 (x : int) (n : nat) : ((term15 x) = (term0 n)) = (x = (term0 n)).
Proof. exact (MK_COMB (@lem2295137 x) (@lem2295138 n)). Qed.
Lemma lem2295142 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2295143 (x : int) (n : nat) : (term18 x n) = (term19 x n).
Proof. exact (MK_COMB (@lem2295142) (@lem2295139 x n)). Qed.
Lemma lem2295158 (x : int) : (term20 x) = (term20 x).
Proof. exact (eq_refl (term20 x)). Qed.
Lemma lem2295159 (n : nat) (x : int) : (term21 n x) = (term22 n x).
Proof. exact (MK_COMB (@lem2295143 x n) (@lem2295158 x)). Qed.
Lemma lem2295164 (n : nat) (x : int) : (term22 n x) = (term21 n x).
Proof. exact (SYM (@lem2295159 n x)). Qed.
Lemma lem2295172 (a : int) : (term15 a) = a.
Proof. exact (EQ_MP (@lem2267745 a) (@lem2267744 a)). Qed.
Lemma lem2295173 (x : int) : (term15 x) = x.
Proof. exact (@lem2295172 x). Qed.
Lemma lem2295174 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2295175 (x : int) : (term17 x) = (@eq int x).
Proof. exact (MK_COMB (@lem2295174) (@lem2295173 x)). Qed.
Lemma lem2295176 (n : nat) : (term16 n) = (term16 n).
Proof. exact (eq_refl (term16 n)). Qed.
Lemma lem2295177 (x : int) (n : nat) : ((term15 x) = (term16 n)) = (x = (term16 n)).
Proof. exact (MK_COMB (@lem2295175 x) (@lem2295176 n)). Qed.
Lemma lem2295180 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2295181 (x : int) (n : nat) : (term23 x n) = (term24 x n).
Proof. exact (MK_COMB (@lem2295180) (@lem2295177 x n)). Qed.
Lemma lem2295196 (x : int) : (term20 x) = (term20 x).
Proof. exact (eq_refl (term20 x)). Qed.
Lemma lem2295197 (n : nat) (x : int) : (term25 n x) = (term26 n x).
Proof. exact (MK_COMB (@lem2295181 x n) (@lem2295196 x)). Qed.
Lemma lem2295202 (n : nat) (x : int) : (term26 n x) = (term25 n x).
Proof. exact (SYM (@lem2295197 n x)). Qed.
Lemma lem2295203 (x : int) (n : nat) (h1 : x = (term0 n)) : x = (term0 n).
Proof. exact (h1). Qed.
Lemma lem2295204 : term27 = term27.
Proof. exact (eq_refl term27). Qed.
Lemma lem2295205 (x : int) (n : nat) (h1 : x = (term0 n)) : (term28 x) = (term29 n).
Proof. exact (MK_COMB (@lem2295204) (@lem2295203 x n h1)). Qed.
Lemma lem2295206 (n : nat) : (term29 n) = (term30 n).
Proof. exact (eq_refl (term29 n)). Qed.
Lemma lem2295207 (x : int) : (term31 x) = (term31 x).
Proof. exact (eq_refl (term31 x)). Qed.
Lemma lem2295208 (x : int) (n : nat) : ((term28 x) = (term29 n)) = ((term28 x) = (term30 n)).
Proof. exact (MK_COMB (@lem2295207 x) (@lem2295206 n)). Qed.
Lemma lem2295209 (x : int) : (term28 x) = (term20 x).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem2295210 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2295211 (x : int) : (term31 x) = (term32 x).
Proof. exact (MK_COMB (@lem2295210) (@lem2295209 x)). Qed.
Lemma lem2295212 (n : nat) : (term30 n) = (term30 n).
Proof. exact (eq_refl (term30 n)). Qed.
Lemma lem2295213 (x : int) (n : nat) : ((term28 x) = (term30 n)) = ((term20 x) = (term30 n)).
Proof. exact (MK_COMB (@lem2295211 x) (@lem2295212 n)). Qed.
Lemma lem2295214 (x : int) (n : nat) : ((term28 x) = (term29 n)) = ((term20 x) = (term30 n)).
Proof. exact (TRANS (@lem2295208 x n) (@lem2295213 x n)). Qed.
Lemma lem2295215 (x : int) (n : nat) (h1 : x = (term0 n)) : (term20 x) = (term30 n).
Proof. exact (EQ_MP (@lem2295214 x n) (@lem2295205 x n h1)). Qed.
Lemma lem2295216 (x : int) (n : nat) (h1 : x = (term0 n)) : (term30 n) = (term20 x).
Proof. exact (SYM (@lem2295215 x n h1)). Qed.
Lemma lem2295217 (x : int) (n : nat) (h1 : x = (term16 n)) : x = (term16 n).
Proof. exact (h1). Qed.
Lemma lem2295218 : term27 = term27.
Proof. exact (eq_refl term27). Qed.
Lemma lem2295219 (x : int) (n : nat) (h1 : x = (term16 n)) : (term28 x) = (term33 n).
Proof. exact (MK_COMB (@lem2295218) (@lem2295217 x n h1)). Qed.
Lemma lem2295220 (n : nat) : (term33 n) = (term34 n).
Proof. exact (eq_refl (term33 n)). Qed.
Lemma lem2295221 (x : int) : (term31 x) = (term31 x).
Proof. exact (eq_refl (term31 x)). Qed.
Lemma lem2295222 (x : int) (n : nat) : ((term28 x) = (term33 n)) = ((term28 x) = (term34 n)).
Proof. exact (MK_COMB (@lem2295221 x) (@lem2295220 n)). Qed.
Lemma lem2295223 (x : int) : (term28 x) = (term20 x).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem2295224 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2295225 (x : int) : (term31 x) = (term32 x).
Proof. exact (MK_COMB (@lem2295224) (@lem2295223 x)). Qed.
Lemma lem2295226 (n : nat) : (term34 n) = (term34 n).
Proof. exact (eq_refl (term34 n)). Qed.
Lemma lem2295227 (x : int) (n : nat) : ((term28 x) = (term34 n)) = ((term20 x) = (term34 n)).
Proof. exact (MK_COMB (@lem2295225 x) (@lem2295226 n)). Qed.
Lemma lem2295228 (x : int) (n : nat) : ((term28 x) = (term33 n)) = ((term20 x) = (term34 n)).
Proof. exact (TRANS (@lem2295222 x n) (@lem2295227 x n)). Qed.
Lemma lem2295229 (x : int) (n : nat) (h1 : x = (term16 n)) : (term20 x) = (term34 n).
Proof. exact (EQ_MP (@lem2295228 x n) (@lem2295219 x n h1)). Qed.
Lemma lem2295230 (x : int) (n : nat) (h1 : x = (term16 n)) : (term34 n) = (term20 x).
Proof. exact (SYM (@lem2295229 x n h1)). Qed.
Lemma lem2295240 (n : nat) : (int_of_num n) = (term0 n).
Proof. exact (EQ_MP (@lem2295116 n) (@lem2295115 n)). Qed.
Lemma lem2295241 (n' : nat) : (int_of_num n') = (term0 n').
Proof. exact (@lem2295240 n'). Qed.
Lemma lem2295242 (n : nat) : (term35 n) = (term35 n).
Proof. exact (eq_refl (term35 n)). Qed.
Lemma lem2295243 (n : nat) (n' : nat) : ((term0 n) = (int_of_num n')) = ((term0 n) = (term0 n')).
Proof. exact (MK_COMB (@lem2295242 n) (@lem2295241 n')). Qed.
Lemma lem2295246 (n : nat) : (term36 n) = (term37 n).
Proof. exact (fun_ext (fun n' : nat => @lem2295243 n n')). Qed.
Lemma lem2295247 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2295248 (n : nat) : (term38 n) = (term39 n).
Proof. exact (MK_COMB (@lem2295247) (@lem2295246 n)). Qed.
Lemma lem2295253 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2295254 (n : nat) : (term40 n) = (term41 n).
Proof. exact (MK_COMB (@lem2295253) (@lem2295248 n)). Qed.
Lemma lem2295262 (i : int) : (int_neg i) = (term9 i).
Proof. exact (EQ_MP (@lem2295113 i) (@lem2295112 i)). Qed.
Lemma lem2295263 (n' : nat) : (term42 n') = (term43 n').
Proof. exact (@lem2295262 (int_of_num n')). Qed.
Lemma lem2295265 (n : nat) : (int_of_num n) = (term0 n).
Proof. exact (EQ_MP (@lem2295116 n) (@lem2295115 n)). Qed.
Lemma lem2295266 (n' : nat) : (int_of_num n') = (term0 n').
Proof. exact (@lem2295265 n'). Qed.
Lemma lem2295267 : real_of_int = real_of_int.
Proof. exact (eq_refl real_of_int). Qed.
Lemma lem2295268 (n' : nat) : (term6 n') = (term44 n').
Proof. exact (MK_COMB (@lem2295267) (@lem2295266 n')). Qed.
Lemma lem2295269 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2295270 (n' : nat) : (term45 n') = (term46 n').
Proof. exact (MK_COMB (@lem2295269) (@lem2295268 n')). Qed.
Lemma lem2295271 : int_of_real = int_of_real.
Proof. exact (eq_refl int_of_real). Qed.
Lemma lem2295272 (n' : nat) : (term43 n') = (term47 n').
Proof. exact (MK_COMB (@lem2295271) (@lem2295270 n')). Qed.
Lemma lem2295273 (n' : nat) : (term42 n') = (term47 n').
Proof. exact (TRANS (@lem2295263 n') (@lem2295272 n')). Qed.
Lemma lem2295274 (n : nat) : (term35 n) = (term35 n).
Proof. exact (eq_refl (term35 n)). Qed.
Lemma lem2295275 (n : nat) (n' : nat) : ((term0 n) = (term42 n')) = ((term0 n) = (term47 n')).
Proof. exact (MK_COMB (@lem2295274 n) (@lem2295273 n')). Qed.
Lemma lem2295278 (n : nat) : (term48 n) = (term49 n).
Proof. exact (fun_ext (fun n' : nat => @lem2295275 n n')). Qed.
Lemma lem2295279 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2295280 (n : nat) : (term50 n) = (term51 n).
Proof. exact (MK_COMB (@lem2295279) (@lem2295278 n)). Qed.
Lemma lem2295285 (n : nat) : (term30 n) = (term52 n).
Proof. exact (MK_COMB (@lem2295254 n) (@lem2295280 n)). Qed.
Lemma lem2295288 (n : nat) : (term52 n) = (term30 n).
Proof. exact (SYM (@lem2295285 n)). Qed.
Lemma lem2295298 (n : nat) : (int_of_num n) = (term0 n).
Proof. exact (EQ_MP (@lem2295116 n) (@lem2295115 n)). Qed.
Lemma lem2295299 (n' : nat) : (int_of_num n') = (term0 n').
Proof. exact (@lem2295298 n'). Qed.
Lemma lem2295300 (n : nat) : (term53 n) = (term53 n).
Proof. exact (eq_refl (term53 n)). Qed.
Lemma lem2295301 (n : nat) (n' : nat) : ((term16 n) = (int_of_num n')) = ((term16 n) = (term0 n')).
Proof. exact (MK_COMB (@lem2295300 n) (@lem2295299 n')). Qed.
Lemma lem2295304 (n : nat) : (term54 n) = (term55 n).
Proof. exact (fun_ext (fun n' : nat => @lem2295301 n n')). Qed.
Lemma lem2295305 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2295306 (n : nat) : (term56 n) = (term57 n).
Proof. exact (MK_COMB (@lem2295305) (@lem2295304 n)). Qed.
Lemma lem2295311 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2295312 (n : nat) : (term58 n) = (term59 n).
Proof. exact (MK_COMB (@lem2295311) (@lem2295306 n)). Qed.
Lemma lem2295320 (i : int) : (int_neg i) = (term9 i).
Proof. exact (EQ_MP (@lem2295113 i) (@lem2295112 i)). Qed.
Lemma lem2295321 (n' : nat) : (term42 n') = (term43 n').
Proof. exact (@lem2295320 (int_of_num n')). Qed.
Lemma lem2295323 (n : nat) : (int_of_num n) = (term0 n).
Proof. exact (EQ_MP (@lem2295116 n) (@lem2295115 n)). Qed.
Lemma lem2295324 (n' : nat) : (int_of_num n') = (term0 n').
Proof. exact (@lem2295323 n'). Qed.
Lemma lem2295325 : real_of_int = real_of_int.
Proof. exact (eq_refl real_of_int). Qed.
Lemma lem2295326 (n' : nat) : (term6 n') = (term44 n').
Proof. exact (MK_COMB (@lem2295325) (@lem2295324 n')). Qed.
Lemma lem2295327 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2295328 (n' : nat) : (term45 n') = (term46 n').
Proof. exact (MK_COMB (@lem2295327) (@lem2295326 n')). Qed.
Lemma lem2295329 : int_of_real = int_of_real.
Proof. exact (eq_refl int_of_real). Qed.
Lemma lem2295330 (n' : nat) : (term43 n') = (term47 n').
Proof. exact (MK_COMB (@lem2295329) (@lem2295328 n')). Qed.
Lemma lem2295331 (n' : nat) : (term42 n') = (term47 n').
Proof. exact (TRANS (@lem2295321 n') (@lem2295330 n')). Qed.
Lemma lem2295332 (n : nat) : (term53 n) = (term53 n).
Proof. exact (eq_refl (term53 n)). Qed.
Lemma lem2295333 (n : nat) (n' : nat) : ((term16 n) = (term42 n')) = ((term16 n) = (term47 n')).
Proof. exact (MK_COMB (@lem2295332 n) (@lem2295331 n')). Qed.
Lemma lem2295336 (n : nat) : (term60 n) = (term61 n).
Proof. exact (fun_ext (fun n' : nat => @lem2295333 n n')). Qed.
Lemma lem2295337 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2295338 (n : nat) : (term62 n) = (term63 n).
Proof. exact (MK_COMB (@lem2295337) (@lem2295336 n)). Qed.
Lemma lem2295343 (n : nat) : (term34 n) = (term64 n).
Proof. exact (MK_COMB (@lem2295312 n) (@lem2295338 n)). Qed.
Lemma lem2295346 (n : nat) : (term64 n) = (term34 n).
Proof. exact (SYM (@lem2295343 n)). Qed.
Lemma lem2295348 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2295349 (x : int) : (x = x) = True.
Proof. exact (@lem2295348 int x). Qed.
Lemma lem2295350 (n : nat) : ((term0 n) = (term0 n)) = True.
Proof. exact (@lem2295349 (term0 n)). Qed.
Lemma lem2295351 (n : nat) : True = ((term0 n) = (term0 n)).
Proof. exact (SYM (@lem2295350 n)). Qed.
Lemma lem2295352 (n : nat) : (term0 n) = (term0 n).
Proof. exact (EQ_MP (@lem2295351 n) (@lem0)). Qed.
Lemma lem2295360 (n : nat) : (term0 n) = (int_of_num n).
Proof. exact (EQ_MP (@lem2295110 n) (@lem2295109 n)). Qed.
Lemma lem2295361 : real_of_int = real_of_int.
Proof. exact (eq_refl real_of_int). Qed.
Lemma lem2295362 (n : nat) : (term44 n) = (term6 n).
Proof. exact (MK_COMB (@lem2295361) (@lem2295360 n)). Qed.
Lemma lem2295364 (n : nat) : (term6 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2295107 n) (@lem2295106 n)). Qed.
Lemma lem2295365 (n : nat) : (term44 n) = (real_of_num n).
Proof. exact (TRANS (@lem2295362 n) (@lem2295364 n)). Qed.
Lemma lem2295366 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2295367 (n : nat) : (term46 n) = (term14 n).
Proof. exact (MK_COMB (@lem2295366) (@lem2295365 n)). Qed.
Lemma lem2295368 : int_of_real = int_of_real.
Proof. exact (eq_refl int_of_real). Qed.
Lemma lem2295369 (n : nat) : (term47 n) = (term16 n).
Proof. exact (MK_COMB (@lem2295368) (@lem2295367 n)). Qed.
Lemma lem2295370 (n : nat) : (term53 n) = (term53 n).
Proof. exact (eq_refl (term53 n)). Qed.
Lemma lem2295371 (n : nat) : ((term16 n) = (term47 n)) = ((term16 n) = (term16 n)).
Proof. exact (MK_COMB (@lem2295370 n) (@lem2295369 n)). Qed.
Lemma lem2295373 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2295374 (x : int) : (x = x) = True.
Proof. exact (@lem2295373 int x). Qed.
Lemma lem2295375 (n : nat) : ((term16 n) = (term16 n)) = True.
Proof. exact (@lem2295374 (term16 n)). Qed.
Lemma lem2295376 (n : nat) : ((term16 n) = (term47 n)) = True.
Proof. exact (TRANS (@lem2295371 n) (@lem2295375 n)). Qed.
Lemma lem2295377 (n : nat) : True = ((term16 n) = (term47 n)).
Proof. exact (SYM (@lem2295376 n)). Qed.
Lemma lem2295379 (n : nat) : (term16 n) = (term47 n).
Proof. exact (EQ_MP (@lem2295377 n) (@lem0)). Qed.
Lemma lem2295380 (n : nat) : term63 n.
Proof. exact (ex_intro (term61 n) n (@lem2295379 n)). Qed.
Lemma lem2295381 (n : nat) : term39 n.
Proof. exact (ex_intro (term37 n) n (@lem2295352 n)). Qed.
Lemma lem2295382 (n : nat) : term64 n.
Proof. exact (or_intro2 (term57 n) (@lem2295380 n)). Qed.
Lemma lem2295383 (n : nat) : term52 n.
Proof. exact (or_intro1 (@lem2295381 n) (term51 n)). Qed.
Lemma lem2295384 (n : nat) : term34 n.
Proof. exact (EQ_MP (@lem2295346 n) (@lem2295382 n)). Qed.
Lemma lem2295385 (n : nat) : term30 n.
Proof. exact (EQ_MP (@lem2295288 n) (@lem2295383 n)). Qed.
Lemma lem2295386 (x : int) (n : nat) (h1 : x = (term16 n)) : term20 x.
Proof. exact (EQ_MP (@lem2295230 x n h1) (@lem2295384 n)). Qed.
Lemma lem2295387 (n : nat) (x : int) : term26 n x.
Proof. exact (fun h0 : x = (term16 n) => @lem2295386 x n h0). Qed.
Lemma lem2295388 (x : int) (n : nat) (h1 : x = (term0 n)) : term20 x.
Proof. exact (EQ_MP (@lem2295216 x n h1) (@lem2295385 n)). Qed.
Lemma lem2295389 (n : nat) (x : int) : term22 n x.
Proof. exact (fun h0 : x = (term0 n) => @lem2295388 x n h0). Qed.
Lemma lem2295390 (n : nat) (x : int) : term25 n x.
Proof. exact (EQ_MP (@lem2295202 n x) (@lem2295387 n x)). Qed.
Lemma lem2295391 (n : nat) (x : int) : term21 n x.
Proof. exact (EQ_MP (@lem2295164 n x) (@lem2295389 n x)). Qed.
Lemma lem2295392 (x : int) (n : nat) (h1 : (real_of_int x) = (term14 n)) : term20 x.
Proof. exact (@lem2295390 n x (@lem2295126 x n h1)). Qed.
Lemma lem2295393 (x : int) (n : nat) (h1 : (real_of_int x) = (real_of_num n)) : term20 x.
Proof. exact (@lem2295391 n x (@lem2295125 x n h1)). Qed.
Lemma lem2295394 (x : int) (n : nat) (h1 : term13 x n) : term20 x.
Proof. exact (or_elim (@lem2295122 x n h1) (fun h0 : (real_of_int x) = (real_of_num n) => @lem2295393 x n h0) (fun h0 : (real_of_int x) = (term14 n) => @lem2295392 x n h0)). Qed.
Lemma lem2295395 (x : int) : term20 x.
Proof. exact (ex_elim (@lem2295121 x) (fun n : nat => fun h0 : term65 x n => @lem2295394 x n h0)). Qed.
Lemma lem2295400 : term66.
Proof. exact (fun x : int => @lem2295395 x). Qed.
