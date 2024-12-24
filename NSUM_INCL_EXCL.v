Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_INCL_EXCL_term_abbrevs.
Require Import ITERATE_INCL_EXCL_spec.
Require Import MONOIDAL_ADD_spec.
Require Import thm0_spec.
Require Import thm6920357_spec.
Require Import thm6920371_spec.
Require Import thm7_spec.
Lemma lem6929991 : (@monoidal nat Nat.add) = ((@monoidal nat Nat.add) = True).
Proof. exact (@lem7 (@monoidal nat Nat.add)). Qed.
Lemma lem6929993 {_120960 _120978 : Type'} (h1 : term0 _120960 _120978) : term0 _120960 _120978.
Proof. exact (h1). Qed.
Lemma lem6929994 {_120960 _120978 : Type'} (op : type1400 _120978) (h1 : term0 _120960 _120978) : term1 _120960 _120978 op.
Proof. exact (@lem6929993 _120960 _120978 h1 op). Qed.
Lemma lem6929995 {_120960 _120978 : Type'} (op : type1400 _120978) : (term1 _120960 _120978 op) = (term2 _120960 _120978 op).
Proof. exact (eq_refl (term1 _120960 _120978 op)). Qed.
Lemma lem6929996 {_120960 _120978 : Type'} (op : type1400 _120978) (h1 : term0 _120960 _120978) : term2 _120960 _120978 op.
Proof. exact (EQ_MP (@lem6929995 _120960 _120978 op) (@lem6929994 _120960 _120978 op h1)). Qed.
Lemma lem6929997 {_120978 : Type'} (op : type1400 _120978) (h1 : @monoidal _120978 op) : @monoidal _120978 op.
Proof. exact (h1). Qed.
Lemma lem6929998 {_120960 _120978 : Type'} (op : type1400 _120978) (h1 : term0 _120960 _120978) (h2 : @monoidal _120978 op) : term3 _120960 _120978 op.
Proof. exact (@lem6929996 _120960 _120978 op h1 (@lem6929997 _120978 op h2)). Qed.
Lemma lem6929999 {_120960 _120978 : Type'} (op : type1400 _120978) (h1 : @monoidal _120978 op) : term4 _120960 _120978 op.
Proof. exact (fun h0 : term0 _120960 _120978 => @lem6929998 _120960 _120978 op h0 h1). Qed.
Lemma lem6930000 {_120960 _120978 : Type'} (h1 : term0 _120960 _120978) : term0 _120960 _120978.
Proof. exact (h1). Qed.
Lemma lem6930001 {_120960 _120978 : Type'} (op : type1400 _120978) (h1 : term0 _120960 _120978) (h2 : @monoidal _120978 op) : term3 _120960 _120978 op.
Proof. exact (@lem6929999 _120960 _120978 op h2 (@lem6930000 _120960 _120978 h1)). Qed.
Lemma lem6930002 {_120960 _120978 : Type'} (op : type1400 _120978) (h1 : term0 _120960 _120978) : term2 _120960 _120978 op.
Proof. exact (fun h0 : @monoidal _120978 op => @lem6930001 _120960 _120978 op h1 h0). Qed.
Lemma lem6930003 {_120960 _120978 : Type'} (h1 : term0 _120960 _120978) : term0 _120960 _120978.
Proof. exact (fun op : type1400 _120978 => @lem6930002 _120960 _120978 op h1). Qed.
Lemma lem6930004 {_120960 _120978 : Type'} : term5 _120960 _120978.
Proof. exact (fun h0 : term0 _120960 _120978 => @lem6930003 _120960 _120978 h0). Qed.
Lemma lem6930005 {_120960 _120978 : Type'} : term0 _120960 _120978.
Proof. exact (@lem6930004 _120960 _120978 (@lem5778669 _120960 _120978)). Qed.
Lemma lem6930006 {_120960 _120978 : Type'} (op : type1400 _120978) : term1 _120960 _120978 op.
Proof. exact (@lem6930005 _120960 _120978 op). Qed.
Lemma lem6930007 {_120960 _120978 : Type'} (op : type1400 _120978) : (term1 _120960 _120978 op) = (term2 _120960 _120978 op).
Proof. exact (eq_refl (term1 _120960 _120978 op)). Qed.
Lemma lem6930034 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6930035 {A : Type'} : (@nsum A) = (@iterate nat A Nat.add).
Proof. exact (@lem6930034 A). Qed.
Lemma lem6930036 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6930037 {A : Type'} (s : A -> Prop) : (@nsum A s) = (@iterate nat A Nat.add s).
Proof. exact (MK_COMB (@lem6930035 A) (@lem6930036 A s)). Qed.
Lemma lem6930038 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6930039 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@nsum A s f) = (@iterate nat A Nat.add s f).
Proof. exact (MK_COMB (@lem6930037 A s) (@lem6930038 A f)). Qed.
Lemma lem6930040 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem6930041 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term6 A s f) = (term7 A s f).
Proof. exact (MK_COMB (@lem6930040) (@lem6930039 A s f)). Qed.
Lemma lem6930043 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6930044 {A : Type'} : (@nsum A) = (@iterate nat A Nat.add).
Proof. exact (@lem6930043 A). Qed.
Lemma lem6930045 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem6930046 {A : Type'} (t : A -> Prop) : (@nsum A t) = (@iterate nat A Nat.add t).
Proof. exact (MK_COMB (@lem6930044 A) (@lem6930045 A t)). Qed.
Lemma lem6930047 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6930048 {A : Type'} (t : A -> Prop) (f : A -> nat) : (@nsum A t f) = (@iterate nat A Nat.add t f).
Proof. exact (MK_COMB (@lem6930046 A t) (@lem6930047 A f)). Qed.
Lemma lem6930049 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> nat) : (term8 A s t f) = (term9 A s t f).
Proof. exact (MK_COMB (@lem6930041 A s f) (@lem6930048 A t f)). Qed.
Lemma lem6930050 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6930051 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> nat) : (term10 A s t f) = (term11 A s t f).
Proof. exact (MK_COMB (@lem6930050) (@lem6930049 A s t f)). Qed.
Lemma lem6930053 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6930054 {A : Type'} : (@nsum A) = (@iterate nat A Nat.add).
Proof. exact (@lem6930053 A). Qed.
Lemma lem6930055 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@UNION A s t) = (@UNION A s t).
Proof. exact (eq_refl (@UNION A s t)). Qed.
Lemma lem6930056 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term12 A s t) = (term13 A s t).
Proof. exact (MK_COMB (@lem6930054 A) (@lem6930055 A s t)). Qed.
Lemma lem6930057 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6930058 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> nat) : (term14 A s t f) = (term15 A s t f).
Proof. exact (MK_COMB (@lem6930056 A s t) (@lem6930057 A f)). Qed.
Lemma lem6930059 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem6930060 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> nat) : (term16 A s t f) = (term17 A s t f).
Proof. exact (MK_COMB (@lem6930059) (@lem6930058 A s t f)). Qed.
Lemma lem6930062 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6930063 {A : Type'} : (@nsum A) = (@iterate nat A Nat.add).
Proof. exact (@lem6930062 A). Qed.
Lemma lem6930064 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@INTER A s t) = (@INTER A s t).
Proof. exact (eq_refl (@INTER A s t)). Qed.
Lemma lem6930065 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term18 A s t) = (term19 A s t).
Proof. exact (MK_COMB (@lem6930063 A) (@lem6930064 A s t)). Qed.
Lemma lem6930066 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6930067 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> nat) : (term20 A s t f) = (term21 A s t f).
Proof. exact (MK_COMB (@lem6930065 A s t) (@lem6930066 A f)). Qed.
Lemma lem6930068 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> nat) : (term22 A s t f) = (term23 A s t f).
Proof. exact (MK_COMB (@lem6930060 A s t f) (@lem6930067 A s t f)). Qed.
Lemma lem6930069 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> nat) : ((term8 A s t f) = (term22 A s t f)) = ((term9 A s t f) = (term23 A s t f)).
Proof. exact (MK_COMB (@lem6930051 A s t f) (@lem6930068 A s t f)). Qed.
Lemma lem6930072 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term24 A s t) = (term24 A s t).
Proof. exact (eq_refl (term24 A s t)). Qed.
Lemma lem6930073 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> nat) : (term25 A s t f) = (term26 A s t f).
Proof. exact (MK_COMB (@lem6930072 A s t) (@lem6930069 A s t f)). Qed.
Lemma lem6930076 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term27 A s t) = (term28 A s t).
Proof. exact (fun_ext (fun f : A -> nat => @lem6930073 A s t f)). Qed.
Lemma lem6930077 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6930078 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term29 A s t) = (term30 A s t).
Proof. exact (MK_COMB (@lem6930077 A) (@lem6930076 A s t)). Qed.
Lemma lem6930083 {A : Type'} (s : A -> Prop) : (term31 A s) = (term32 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem6930078 A s t)). Qed.
Lemma lem6930084 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6930085 {A : Type'} (s : A -> Prop) : (term33 A s) = (term34 A s).
Proof. exact (MK_COMB (@lem6930084 A) (@lem6930083 A s)). Qed.
Lemma lem6930090 {A : Type'} : (term35 A) = (term36 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6930085 A s)). Qed.
Lemma lem6930091 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6930092 {A : Type'} : (term37 A) = (term38 A).
Proof. exact (MK_COMB (@lem6930091 A) (@lem6930090 A)). Qed.
Lemma lem6930097 {A : Type'} : (term38 A) = (term37 A).
Proof. exact (SYM (@lem6930092 A)). Qed.
Lemma lem6930099 {_120960 _120978 : Type'} (op : type1400 _120978) : term2 _120960 _120978 op.
Proof. exact (EQ_MP (@lem6930007 _120960 _120978 op) (@lem6930006 _120960 _120978 op)). Qed.
Lemma lem6930100 {A : Type'} (op : type1606) : term39 A op.
Proof. exact (@lem6930099 A nat op). Qed.
Lemma lem6930101 {A : Type'} : term40 A.
Proof. exact (@lem6930100 A Nat.add). Qed.
Lemma lem6930103 : (@monoidal nat Nat.add) = True.
Proof. exact (EQ_MP (@lem6929991) (@lem6924403)). Qed.
Lemma lem6930104 : True = (@monoidal nat Nat.add).
Proof. exact (SYM (@lem6930103)). Qed.
Lemma lem6930105 : @monoidal nat Nat.add.
Proof. exact (EQ_MP (@lem6930104) (@lem0)). Qed.
Lemma lem6930106 {A : Type'} : term38 A.
Proof. exact (@lem6930101 A (@lem6930105)). Qed.
Lemma lem6930107 {A : Type'} : term37 A.
Proof. exact (EQ_MP (@lem6930097 A) (@lem6930106 A)). Qed.
