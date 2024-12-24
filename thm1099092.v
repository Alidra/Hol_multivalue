Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1099092_term_abbrevs.
Require Import SKOLEM_THM_spec.
Require Import thm75635_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem1098976 {_25272 : Type'} (REPLICATE' : type1595 _25272) (h1 : (term0 _25272 REPLICATE') = (term1 _25272)) : (term0 _25272 REPLICATE') = (term1 _25272).
Proof. exact (h1). Qed.
Lemma lem1098977 {_25272 : Type'} (x : _25272) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1098978 {_25272 : Type'} (x : _25272) (REPLICATE' : type1595 _25272) (h1 : (term0 _25272 REPLICATE') = (term1 _25272)) : (term2 _25272 REPLICATE' x) = (term3 _25272 x).
Proof. exact (MK_COMB (@lem1098976 _25272 REPLICATE' h1) (@lem1098977 _25272 x)). Qed.
Lemma lem1098979 {_25272 : Type'} (x : _25272) : (term3 _25272 x) = (@nil _25272).
Proof. exact (eq_refl (term3 _25272 x)). Qed.
Lemma lem1098980 {_25272 : Type'} (REPLICATE' : type1595 _25272) (x : _25272) : (term4 _25272 REPLICATE' x) = (term4 _25272 REPLICATE' x).
Proof. exact (eq_refl (term4 _25272 REPLICATE' x)). Qed.
Lemma lem1098981 {_25272 : Type'} (REPLICATE' : type1595 _25272) (x : _25272) : ((term2 _25272 REPLICATE' x) = (term3 _25272 x)) = ((term2 _25272 REPLICATE' x) = (@nil _25272)).
Proof. exact (MK_COMB (@lem1098980 _25272 REPLICATE' x) (@lem1098979 _25272 x)). Qed.
Lemma lem1098982 {_25272 : Type'} (x : _25272) (REPLICATE' : type1595 _25272) (h1 : (term0 _25272 REPLICATE') = (term1 _25272)) : (term2 _25272 REPLICATE' x) = (@nil _25272).
Proof. exact (EQ_MP (@lem1098981 _25272 REPLICATE' x) (@lem1098978 _25272 x REPLICATE' h1)). Qed.
Lemma lem1098983 {_25272 : Type'} (REPLICATE' : type1595 _25272) (h1 : (term0 _25272 REPLICATE') = (term1 _25272)) : term5 _25272 REPLICATE'.
Proof. exact (fun x : _25272 => @lem1098982 _25272 x REPLICATE' h1). Qed.
Lemma lem1098984 {_25272 : Type'} (REPLICATE' : type1595 _25272) (h1 : term6 _25272 REPLICATE') : term6 _25272 REPLICATE'.
Proof. exact (h1). Qed.
Lemma lem1098985 {_25272 : Type'} (n : nat) (REPLICATE' : type1595 _25272) (h1 : term6 _25272 REPLICATE') : term7 _25272 REPLICATE' n.
Proof. exact (@lem1098984 _25272 REPLICATE' h1 n). Qed.
Lemma lem1098986 {_25272 : Type'} (REPLICATE' : type1595 _25272) (n : nat) : (term7 _25272 REPLICATE' n) = ((term8 _25272 REPLICATE' n) = (term9 _25272 REPLICATE' n)).
Proof. exact (eq_refl (term7 _25272 REPLICATE' n)). Qed.
Lemma lem1098987 {_25272 : Type'} (n : nat) (REPLICATE' : type1595 _25272) (h1 : term6 _25272 REPLICATE') : (term8 _25272 REPLICATE' n) = (term9 _25272 REPLICATE' n).
Proof. exact (EQ_MP (@lem1098986 _25272 REPLICATE' n) (@lem1098985 _25272 n REPLICATE' h1)). Qed.
Lemma lem1098988 {_25272 : Type'} (x : _25272) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1098989 {_25272 : Type'} (n : nat) (x : _25272) (REPLICATE' : type1595 _25272) (h1 : term6 _25272 REPLICATE') : (term10 _25272 REPLICATE' n x) = (term11 _25272 REPLICATE' n x).
Proof. exact (MK_COMB (@lem1098987 _25272 n REPLICATE' h1) (@lem1098988 _25272 x)). Qed.
Lemma lem1098990 {_25272 : Type'} (REPLICATE' : type1595 _25272) (n : nat) (x : _25272) : (term11 _25272 REPLICATE' n x) = (term12 _25272 REPLICATE' n x).
Proof. exact (eq_refl (term11 _25272 REPLICATE' n x)). Qed.
Lemma lem1098991 {_25272 : Type'} (REPLICATE' : type1595 _25272) (n : nat) (x : _25272) : (term13 _25272 REPLICATE' n x) = (term13 _25272 REPLICATE' n x).
Proof. exact (eq_refl (term13 _25272 REPLICATE' n x)). Qed.
Lemma lem1098992 {_25272 : Type'} (REPLICATE' : type1595 _25272) (n : nat) (x : _25272) : ((term10 _25272 REPLICATE' n x) = (term11 _25272 REPLICATE' n x)) = ((term10 _25272 REPLICATE' n x) = (term12 _25272 REPLICATE' n x)).
Proof. exact (MK_COMB (@lem1098991 _25272 REPLICATE' n x) (@lem1098990 _25272 REPLICATE' n x)). Qed.
Lemma lem1098993 {_25272 : Type'} (n : nat) (x : _25272) (REPLICATE' : type1595 _25272) (h1 : term6 _25272 REPLICATE') : (term10 _25272 REPLICATE' n x) = (term12 _25272 REPLICATE' n x).
Proof. exact (EQ_MP (@lem1098992 _25272 REPLICATE' n x) (@lem1098989 _25272 n x REPLICATE' h1)). Qed.
Lemma lem1098994 {_25272 : Type'} (n : nat) (REPLICATE' : type1595 _25272) (h1 : term6 _25272 REPLICATE') : term14 _25272 REPLICATE' n.
Proof. exact (fun x : _25272 => @lem1098993 _25272 n x REPLICATE' h1). Qed.
Lemma lem1098995 {_25272 : Type'} (REPLICATE' : type1595 _25272) (h1 : term6 _25272 REPLICATE') : term15 _25272 REPLICATE'.
Proof. exact (fun n : nat => @lem1098994 _25272 n REPLICATE' h1). Qed.
Lemma lem1098996 {_25272 : Type'} (REPLICATE' : type1595 _25272) (h1 : term16 _25272 REPLICATE') : term16 _25272 REPLICATE'.
Proof. exact (h1). Qed.
Lemma lem1098997 {_25272 : Type'} (REPLICATE' : type1595 _25272) (h1 : term16 _25272 REPLICATE') : term6 _25272 REPLICATE'.
Proof. exact (proj2 (@lem1098996 _25272 REPLICATE' h1)). Qed.
Lemma lem1098998 {_25272 : Type'} (REPLICATE' : type1595 _25272) (h1 : term16 _25272 REPLICATE') : (term0 _25272 REPLICATE') = (term1 _25272).
Proof. exact (proj1 (@lem1098996 _25272 REPLICATE' h1)). Qed.
Lemma lem1098999 {_25272 : Type'} (REPLICATE' : type1595 _25272) (h1 : term16 _25272 REPLICATE') : ((term0 _25272 REPLICATE') = (term1 _25272)) = (term5 _25272 REPLICATE').
Proof. exact (prop_ext (fun h2 : (term0 _25272 REPLICATE') = (term1 _25272) => @lem1098983 _25272 REPLICATE' h2) (fun h2 : term5 _25272 REPLICATE' => @lem1098998 _25272 REPLICATE' h1)). Qed.
Lemma lem1099000 {_25272 : Type'} (REPLICATE' : type1595 _25272) (h1 : term16 _25272 REPLICATE') : term5 _25272 REPLICATE'.
Proof. exact (EQ_MP (@lem1098999 _25272 REPLICATE' h1) (@lem1098998 _25272 REPLICATE' h1)). Qed.
Lemma lem1099001 {_25272 : Type'} (REPLICATE' : type1595 _25272) (h1 : term16 _25272 REPLICATE') : (term6 _25272 REPLICATE') = (term15 _25272 REPLICATE').
Proof. exact (prop_ext (fun h2 : term6 _25272 REPLICATE' => @lem1098995 _25272 REPLICATE' h2) (fun h2 : term15 _25272 REPLICATE' => @lem1098997 _25272 REPLICATE' h1)). Qed.
Lemma lem1099002 {_25272 : Type'} (REPLICATE' : type1595 _25272) (h1 : term16 _25272 REPLICATE') : term15 _25272 REPLICATE'.
Proof. exact (EQ_MP (@lem1099001 _25272 REPLICATE' h1) (@lem1098997 _25272 REPLICATE' h1)). Qed.
Lemma lem1099003 {_25272 : Type'} (REPLICATE' : type1595 _25272) (h1 : term16 _25272 REPLICATE') : term17 _25272 REPLICATE'.
Proof. exact (conj (@lem1099000 _25272 REPLICATE' h1) (@lem1099002 _25272 REPLICATE' h1)). Qed.
Lemma lem1099004 {A : Type'} (e : A) : term18 A e.
Proof. exact (@lem75635 A e). Qed.
Lemma lem1099005 {A : Type'} (e : A) : (term18 A e) = (term19 A e).
Proof. exact (eq_refl (term18 A e)). Qed.
Lemma lem1099006 {A : Type'} (e : A) : term19 A e.
Proof. exact (EQ_MP (@lem1099005 A e) (@lem1099004 A e)). Qed.
Lemma lem1099007 {A : Type'} (e : A) (f : type1423 A) : term20 A e f.
Proof. exact (@lem1099006 A e f). Qed.
Lemma lem1099008 {A : Type'} (e : A) (f : type1423 A) : (term20 A e f) = (term21 A e f).
Proof. exact (eq_refl (term20 A e f)). Qed.
Lemma lem1099009 {A : Type'} (e : A) (f : type1423 A) : term21 A e f.
Proof. exact (EQ_MP (@lem1099008 A e f) (@lem1099007 A e f)). Qed.
Lemma lem1099010 {_25272 : Type'} (e : type1427 _25272) (f : type477 _25272) : term22 _25272 e f.
Proof. exact (@lem1099009 (type1427 _25272) e f). Qed.
Lemma lem1099011 {_25272 : Type'} : term23 _25272.
Proof. exact (@lem1099010 _25272 (term1 _25272) (term24 _25272)). Qed.
Lemma lem1099012 {_25272 : Type'} (fn : type1595 _25272) (n : nat) : (term25 _25272 fn n) = (term26 _25272 fn n).
Proof. exact (eq_refl (term25 _25272 fn n)). Qed.
Lemma lem1099013 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1099014 {_25272 : Type'} (fn : type1595 _25272) (n : nat) : (term27 _25272 fn n) = (term28 _25272 fn n).
Proof. exact (MK_COMB (@lem1099012 _25272 fn n) (@lem1099013 n)). Qed.
Lemma lem1099015 {_25272 : Type'} (fn : type1595 _25272) (n : nat) : (term28 _25272 fn n) = (term9 _25272 fn n).
Proof. exact (eq_refl (term28 _25272 fn n)). Qed.
Lemma lem1099016 {_25272 : Type'} (fn : type1595 _25272) (n : nat) : (term27 _25272 fn n) = (term9 _25272 fn n).
Proof. exact (TRANS (@lem1099014 _25272 fn n) (@lem1099015 _25272 fn n)). Qed.
Lemma lem1099017 {_25272 : Type'} (fn : type1595 _25272) (n : nat) : (term29 _25272 fn n) = (term29 _25272 fn n).
Proof. exact (eq_refl (term29 _25272 fn n)). Qed.
Lemma lem1099018 {_25272 : Type'} (fn : type1595 _25272) (n : nat) : ((term8 _25272 fn n) = (term27 _25272 fn n)) = ((term8 _25272 fn n) = (term9 _25272 fn n)).
Proof. exact (MK_COMB (@lem1099017 _25272 fn n) (@lem1099016 _25272 fn n)). Qed.
Lemma lem1099019 {_25272 : Type'} (fn : type1595 _25272) : (term30 _25272 fn) = (term31 _25272 fn).
Proof. exact (fun_ext (fun n : nat => @lem1099018 _25272 fn n)). Qed.
Lemma lem1099020 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1099021 {_25272 : Type'} (fn : type1595 _25272) : (term32 _25272 fn) = (term6 _25272 fn).
Proof. exact (MK_COMB (@lem1099020) (@lem1099019 _25272 fn)). Qed.
Lemma lem1099022 {_25272 : Type'} (fn : type1595 _25272) : (term33 _25272 fn) = (term33 _25272 fn).
Proof. exact (eq_refl (term33 _25272 fn)). Qed.
Lemma lem1099023 {_25272 : Type'} (fn : type1595 _25272) : (term34 _25272 fn) = (term16 _25272 fn).
Proof. exact (MK_COMB (@lem1099022 _25272 fn) (@lem1099021 _25272 fn)). Qed.
Lemma lem1099024 {_25272 : Type'} : (term35 _25272) = (term36 _25272).
Proof. exact (fun_ext (fun fn : type1595 _25272 => @lem1099023 _25272 fn)). Qed.
Lemma lem1099025 {_25272 : Type'} : (@ex (nat -> _25272 -> list _25272)) = (@ex (nat -> _25272 -> list _25272)).
Proof. exact (eq_refl (@ex (nat -> _25272 -> list _25272))). Qed.
Lemma lem1099026 {_25272 : Type'} : (term23 _25272) = (term37 _25272).
Proof. exact (MK_COMB (@lem1099025 _25272) (@lem1099024 _25272)). Qed.
Lemma lem1099027 {_25272 : Type'} : term37 _25272.
Proof. exact (EQ_MP (@lem1099026 _25272) (@lem1099011 _25272)). Qed.
Lemma lem1099028 {_25272 : Type'} (REPLICATE' : type1595 _25272) (h1 : term16 _25272 REPLICATE') : term16 _25272 REPLICATE'.
Proof. exact (h1). Qed.
Lemma lem1099029 {_25272 : Type'} (REPLICATE' : type1595 _25272) (h1 : term16 _25272 REPLICATE') : term6 _25272 REPLICATE'.
Proof. exact (proj2 (@lem1099028 _25272 REPLICATE' h1)). Qed.
Lemma lem1099030 {_25272 : Type'} (REPLICATE' : type1595 _25272) (h1 : term16 _25272 REPLICATE') : (term0 _25272 REPLICATE') = (term1 _25272).
Proof. exact (proj1 (@lem1099028 _25272 REPLICATE' h1)). Qed.
Lemma lem1099031 {_25272 : Type'} (REPLICATE' : type1595 _25272) (h1 : term16 _25272 REPLICATE') : term16 _25272 REPLICATE'.
Proof. exact (conj (@lem1099030 _25272 REPLICATE' h1) (@lem1099029 _25272 REPLICATE' h1)). Qed.
Lemma lem1099032 {_25272 : Type'} (REPLICATE' : type1595 _25272) (h1 : term16 _25272 REPLICATE') : term37 _25272.
Proof. exact (ex_intro (term36 _25272) REPLICATE' (@lem1099031 _25272 REPLICATE' h1)). Qed.
Lemma lem1099033 {_25272 : Type'} (h1 : term37 _25272) : term37 _25272.
Proof. exact (h1). Qed.
Lemma lem1099034 {_25272 : Type'} (h1 : term37 _25272) : term37 _25272.
Proof. exact (ex_elim (@lem1099033 _25272 h1) (fun REPLICATE' : type1595 _25272 => fun h0 : term36 _25272 REPLICATE' => @lem1099032 _25272 REPLICATE' h0)). Qed.
Lemma lem1099035 {_25272 : Type'} : (term37 _25272) = (term37 _25272).
Proof. exact (prop_ext (fun h1 : term37 _25272 => @lem1099034 _25272 h1) (fun h1 : term37 _25272 => @lem1099027 _25272)). Qed.
Lemma lem1099036 {_25272 : Type'} : term37 _25272.
Proof. exact (EQ_MP (@lem1099035 _25272) (@lem1099027 _25272)). Qed.
Lemma lem1099037 {_25272 : Type'} (REPLICATE' : type1595 _25272) (h1 : term16 _25272 REPLICATE') : term38 _25272.
Proof. exact (ex_intro (term39 _25272) REPLICATE' (@lem1099003 _25272 REPLICATE' h1)). Qed.
Lemma lem1099038 {_25272 : Type'} (h1 : term37 _25272) : term37 _25272.
Proof. exact (h1). Qed.
Lemma lem1099039 {_25272 : Type'} (h1 : term37 _25272) : term38 _25272.
Proof. exact (ex_elim (@lem1099038 _25272 h1) (fun REPLICATE' : type1595 _25272 => fun h0 : term36 _25272 REPLICATE' => @lem1099037 _25272 REPLICATE' h0)). Qed.
Lemma lem1099040 {_25272 : Type'} : (term37 _25272) = (term38 _25272).
Proof. exact (prop_ext (fun h1 : term37 _25272 => @lem1099039 _25272 h1) (fun h1 : term38 _25272 => @lem1099036 _25272)). Qed.
Lemma lem1099041 {_25272 : Type'} : term38 _25272.
Proof. exact (EQ_MP (@lem1099040 _25272) (@lem1099036 _25272)). Qed.
Lemma lem1099044 {_25272 : Type'} (REPLICATE' : type1595 _25272) (h1 : term17 _25272 REPLICATE') : term17 _25272 REPLICATE'.
Proof. exact (h1). Qed.
Lemma lem1099045 {_25272 : Type'} (REPLICATE' : type1595 _25272) (h1 : term17 _25272 REPLICATE') : term38 _25272.
Proof. exact (ex_intro (term39 _25272) REPLICATE' (@lem1099044 _25272 REPLICATE' h1)). Qed.
Lemma lem1099046 {_25272 : Type'} (h1 : term38 _25272) : term38 _25272.
Proof. exact (h1). Qed.
Lemma lem1099047 {_25272 : Type'} (h1 : term38 _25272) : term38 _25272.
Proof. exact (ex_elim (@lem1099046 _25272 h1) (fun REPLICATE' : type1595 _25272 => fun h0 : term39 _25272 REPLICATE' => @lem1099045 _25272 REPLICATE' h0)). Qed.
Lemma lem1099048 {_25272 : Type'} : (term38 _25272) = (term38 _25272).
Proof. exact (prop_ext (fun h1 : term38 _25272 => @lem1099047 _25272 h1) (fun h1 : term38 _25272 => @lem1099041 _25272)). Qed.
Lemma lem1099049 {_25272 : Type'} : term38 _25272.
Proof. exact (EQ_MP (@lem1099048 _25272) (@lem1099041 _25272)). Qed.
Lemma lem1099050 {_25272 : Type'} : term40 _25272.
Proof. exact (fun _17962 : type1668 => @lem1099049 _25272). Qed.
Lemma lem1099051 {A B : Type'} (P : type1413 A B) : term41 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem1099052 {A B : Type'} (P : type1413 A B) : (term41 A B P) = ((term42 A B P) = (term43 A B P)).
Proof. exact (eq_refl (term41 A B P)). Qed.
Lemma lem1099055 {A B : Type'} (P : type1413 A B) : (term42 A B P) = (term43 A B P).
Proof. exact (EQ_MP (@lem1099052 A B P) (@lem1099051 A B P)). Qed.
Lemma lem1099056 {_25272 : Type'} (P : type1239 _25272) : (term44 _25272 P) = (term45 _25272 P).
Proof. exact (@lem1099055 type1668 (type1595 _25272) P). Qed.
Lemma lem1099057 {_25272 : Type'} : (term46 _25272) = (term47 _25272).
Proof. exact (@lem1099056 _25272 (term48 _25272)). Qed.
Lemma lem1099058 {_25272 : Type'} (_17962 : type1668) : (term49 _25272 _17962) = (term39 _25272).
Proof. exact (eq_refl (term49 _25272 _17962)). Qed.
Lemma lem1099059 {_25272 : Type'} (REPLICATE' : type1595 _25272) : REPLICATE' = REPLICATE'.
Proof. exact (eq_refl REPLICATE'). Qed.
Lemma lem1099060 {_25272 : Type'} (_17962 : type1668) (REPLICATE' : type1595 _25272) : (term50 _25272 _17962 REPLICATE') = (term51 _25272 REPLICATE').
Proof. exact (MK_COMB (@lem1099058 _25272 _17962) (@lem1099059 _25272 REPLICATE')). Qed.
Lemma lem1099061 {_25272 : Type'} (REPLICATE' : type1595 _25272) : (term51 _25272 REPLICATE') = (term17 _25272 REPLICATE').
Proof. exact (eq_refl (term51 _25272 REPLICATE')). Qed.
Lemma lem1099062 {_25272 : Type'} (_17962 : type1668) (REPLICATE' : type1595 _25272) : (term50 _25272 _17962 REPLICATE') = (term17 _25272 REPLICATE').
Proof. exact (TRANS (@lem1099060 _25272 _17962 REPLICATE') (@lem1099061 _25272 REPLICATE')). Qed.
Lemma lem1099063 {_25272 : Type'} (_17962 : type1668) : (term52 _25272 _17962) = (term39 _25272).
Proof. exact (fun_ext (fun REPLICATE' : type1595 _25272 => @lem1099062 _25272 _17962 REPLICATE')). Qed.
Lemma lem1099064 {_25272 : Type'} : (@ex (nat -> _25272 -> list _25272)) = (@ex (nat -> _25272 -> list _25272)).
Proof. exact (eq_refl (@ex (nat -> _25272 -> list _25272))). Qed.
Lemma lem1099065 {_25272 : Type'} (_17962 : type1668) : (term53 _25272 _17962) = (term38 _25272).
Proof. exact (MK_COMB (@lem1099064 _25272) (@lem1099063 _25272 _17962)). Qed.
Lemma lem1099066 {_25272 : Type'} : (term54 _25272) = (term55 _25272).
Proof. exact (fun_ext (fun _17962 : type1668 => @lem1099065 _25272 _17962)). Qed.
Lemma lem1099067 : (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) = (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))). Qed.
Lemma lem1099068 {_25272 : Type'} : (term46 _25272) = (term40 _25272).
Proof. exact (MK_COMB (@lem1099067) (@lem1099066 _25272)). Qed.
Lemma lem1099069 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1099070 {_25272 : Type'} : (term56 _25272) = (term57 _25272).
Proof. exact (MK_COMB (@lem1099069) (@lem1099068 _25272)). Qed.
Lemma lem1099071 {_25272 : Type'} (_17962 : type1668) : (term49 _25272 _17962) = (term39 _25272).
Proof. exact (eq_refl (term49 _25272 _17962)). Qed.
Lemma lem1099072 {_25272 : Type'} (REPLICATE' : type1240 _25272) (_17962 : type1668) : (REPLICATE' _17962) = (REPLICATE' _17962).
Proof. exact (eq_refl (REPLICATE' _17962)). Qed.
Lemma lem1099073 {_25272 : Type'} (REPLICATE' : type1240 _25272) (_17962 : type1668) : (term58 _25272 REPLICATE' _17962) = (term59 _25272 REPLICATE' _17962).
Proof. exact (MK_COMB (@lem1099071 _25272 _17962) (@lem1099072 _25272 REPLICATE' _17962)). Qed.
Lemma lem1099074 {_25272 : Type'} (REPLICATE' : type1240 _25272) (_17962 : type1668) : (term59 _25272 REPLICATE' _17962) = (term60 _25272 REPLICATE' _17962).
Proof. exact (eq_refl (term59 _25272 REPLICATE' _17962)). Qed.
Lemma lem1099075 {_25272 : Type'} (REPLICATE' : type1240 _25272) (_17962 : type1668) : (term58 _25272 REPLICATE' _17962) = (term60 _25272 REPLICATE' _17962).
Proof. exact (TRANS (@lem1099073 _25272 REPLICATE' _17962) (@lem1099074 _25272 REPLICATE' _17962)). Qed.
Lemma lem1099076 {_25272 : Type'} (REPLICATE' : type1240 _25272) : (term61 _25272 REPLICATE') = (term62 _25272 REPLICATE').
Proof. exact (fun_ext (fun _17962 : type1668 => @lem1099075 _25272 REPLICATE' _17962)). Qed.
Lemma lem1099077 : (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))) = (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))))). Qed.
Lemma lem1099078 {_25272 : Type'} (REPLICATE' : type1240 _25272) : (term63 _25272 REPLICATE') = (term64 _25272 REPLICATE').
Proof. exact (MK_COMB (@lem1099077) (@lem1099076 _25272 REPLICATE')). Qed.
Lemma lem1099079 {_25272 : Type'} : (term65 _25272) = (term66 _25272).
Proof. exact (fun_ext (fun REPLICATE' : type1240 _25272 => @lem1099078 _25272 REPLICATE')). Qed.
Lemma lem1099080 {_25272 : Type'} : (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) -> nat -> _25272 -> list _25272)) = (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) -> nat -> _25272 -> list _25272)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) -> nat -> _25272 -> list _25272))). Qed.
Lemma lem1099081 {_25272 : Type'} : (term47 _25272) = (term67 _25272).
Proof. exact (MK_COMB (@lem1099080 _25272) (@lem1099079 _25272)). Qed.
Lemma lem1099082 {_25272 : Type'} : ((term46 _25272) = (term47 _25272)) = ((term40 _25272) = (term67 _25272)).
Proof. exact (MK_COMB (@lem1099070 _25272) (@lem1099081 _25272)). Qed.
Lemma lem1099083 {_25272 : Type'} : (term40 _25272) = (term67 _25272).
Proof. exact (EQ_MP (@lem1099082 _25272) (@lem1099057 _25272)). Qed.
Lemma lem1099084 {_25272 : Type'} : term67 _25272.
Proof. exact (EQ_MP (@lem1099083 _25272) (@lem1099050 _25272)). Qed.
Lemma lem1099086 {A : Type'} : (@ex A) = (term68 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem1099087 {_25272 : Type'} : (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))) -> nat -> _25272 -> list _25272)) = (term69 _25272).
Proof. exact (@lem1099086 (type1240 _25272)). Qed.
Lemma lem1099088 {_25272 : Type'} : (term66 _25272) = (term66 _25272).
Proof. exact (eq_refl (term66 _25272)). Qed.
Lemma lem1099089 {_25272 : Type'} : (term67 _25272) = (term70 _25272).
Proof. exact (MK_COMB (@lem1099087 _25272) (@lem1099088 _25272)). Qed.
Lemma lem1099090 {_25272 : Type'} : (term70 _25272) = (term71 _25272).
Proof. exact (eq_refl (term70 _25272)). Qed.
Lemma lem1099091 {_25272 : Type'} : (term67 _25272) = (term71 _25272).
Proof. exact (TRANS (@lem1099089 _25272) (@lem1099090 _25272)). Qed.
Lemma lem1099092 {_25272 : Type'} : term71 _25272.
Proof. exact (EQ_MP (@lem1099091 _25272) (@lem1099084 _25272)). Qed.
