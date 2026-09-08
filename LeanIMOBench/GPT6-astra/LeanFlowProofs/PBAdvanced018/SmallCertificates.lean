import Mathlib

theorem LeanFlowProofs.PB018.small_certificates (n k : ℕ) (hexception : (n, k) ∈ ({(6, 7), (7, 7), (7, 9), (7, 10), (7, 11), (8, 13), (9, 9), (9, 11), (9, 12), (9, 15), (9, 16), (9, 17), (9, 18), (10, 20)} : Finset (ℕ × ℕ))) : ∃ (M : Fin n → Fin n → Fin k) (p : (Fin n × Fin n) → Fin (n * n)), (∀ i : Fin k, (Finset.univ.filter (fun x : Fin n × Fin n => M x.1 x.2 = i)).card = n ^ 2 / k ∨ (Finset.univ.filter (fun x : Fin n × Fin n => M x.1 x.2 = i)).card = n ^ 2 / k + 1) ∧ (∀ b : Fin (n * n), (Finset.univ.filter (fun x : Fin n × Fin n => p x = b)).card < n) ∧ (∀ x y : Fin n × Fin n, abs ((x.2 : ℤ) - (y.2 : ℤ)) + abs ((x.1 : ℤ) - (y.1 : ℤ)) = 1 → M x.1 x.2 ≠ M y.1 y.2 → p x = p y) := by 
  have edges {n k l : ℕ} (M : Fin n → Fin n → Fin k) (p : Fin n × Fin n → Fin l)
      (hh : ∀ i j : Fin n, ∀ h : j.val + 1 < n, M i j ≠ M i ⟨j.val+1,h⟩ → p (i,j) = p (i,⟨j.val+1,h⟩))
      (hv : ∀ i j : Fin n, ∀ h : i.val + 1 < n, M i j ≠ M ⟨i.val+1,h⟩ j → p (i,j) = p (⟨i.val+1,h⟩,j)) :
      ∀ x y : Fin n × Fin n, abs ((x.2 : ℤ) - (y.2 : ℤ)) + abs ((x.1 : ℤ) - (y.1 : ℤ)) = 1 → M x.1 x.2 ≠ M y.1 y.2 → p x = p y := by
    rintro ⟨a,b⟩ ⟨c,d⟩ ha hne
    simp only [abs_eq_max_neg] at ha
    have hc : (a = c ∧ b.val + 1 = d.val) ∨ (a = c ∧ d.val + 1 = b.val) ∨ (b = d ∧ a.val + 1 = c.val) ∨ (b = d ∧ c.val + 1 = a.val) := by
      have : (a.val = c.val ∧ b.val + 1 = d.val) ∨ (a.val = c.val ∧ d.val + 1 = b.val) ∨ (b.val = d.val ∧ a.val + 1 = c.val) ∨ (b.val = d.val ∧ c.val + 1 = a.val) := by omega
      simpa only [Fin.ext_iff] using this
    rcases hc with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · have ht : b.val + 1 < n := by omega
      have he : (⟨b.val+1,ht⟩ : Fin n) = d := Fin.ext h
      simpa only [he] using hh a b ht (by simpa only [he] using hne)
    · have ht : d.val + 1 < n := by omega
      have he : (⟨d.val+1,ht⟩ : Fin n) = b := Fin.ext h
      symm
      simpa only [he] using hh a d ht (by simpa only [he] using Ne.symm hne)
    · have ht : a.val + 1 < n := by omega
      have he : (⟨a.val+1,ht⟩ : Fin n) = c := Fin.ext h
      simpa only [he] using hv a b ht (by simpa only [he] using hne)
    · have ht : c.val + 1 < n := by omega
      have he : (⟨c.val+1,ht⟩ : Fin n) = a := Fin.ext h
      symm
      simpa only [he] using hv c b ht (by simpa only [he] using Ne.symm hne)
  have liftCert {n k : ℕ} (hn : 0 < n) (hl : 16 ≤ n*n) (M : Fin n → Fin n → Fin k) (p : Fin n × Fin n → Fin 16)
      (hb : ∀ i : Fin k, (Finset.univ.filter (fun x : Fin n × Fin n => M x.1 x.2 = i)).card = n^2/k ∨ (Finset.univ.filter (fun x : Fin n × Fin n => M x.1 x.2 = i)).card = n^2/k+1)
      (hs : ∀ b : Fin 16, (Finset.univ.filter (fun x : Fin n × Fin n => p x = b)).card < n)
      (hh : ∀ i j : Fin n, ∀ h : j.val + 1 < n, M i j ≠ M i ⟨j.val+1,h⟩ → p (i,j) = p (i,⟨j.val+1,h⟩))
      (hv : ∀ i j : Fin n, ∀ h : i.val + 1 < n, M i j ≠ M ⟨i.val+1,h⟩ j → p (i,j) = p (⟨i.val+1,h⟩,j)) :
      ∃ (M : Fin n → Fin n → Fin k) (p : Fin n × Fin n → Fin (n*n)), (∀ i : Fin k, (Finset.univ.filter (fun x : Fin n × Fin n => M x.1 x.2 = i)).card = n^2/k ∨ (Finset.univ.filter (fun x : Fin n × Fin n => M x.1 x.2 = i)).card = n^2/k+1) ∧ (∀ b, (Finset.univ.filter (fun x : Fin n × Fin n => p x = b)).card < n) ∧ (∀ x y : Fin n × Fin n, abs ((x.2 : ℤ) - (y.2 : ℤ)) + abs ((x.1 : ℤ) - (y.1 : ℤ)) = 1 → M x.1 x.2 ≠ M y.1 y.2 → p x = p y) := by
    refine ⟨M, fun x => Fin.castLE hl (p x), hb, ?_, ?_⟩
    · intro b
      by_cases h : b.val < 16
      · simpa only [Fin.ext_iff, Fin.val_castLE] using hs ⟨b.val,h⟩
      · have he : (Finset.univ.filter (fun x : Fin n × Fin n => Fin.castLE hl (p x) = b)) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro x _ he
          have hv := congrArg Fin.val he
          have := (p x).isLt
          simp only [Fin.val_castLE] at hv
          omega
        rw [he, Finset.card_empty]
        exact hn
    · intro x y ha hm
      exact congrArg (Fin.castLE hl) (edges M p hh hv x y ha hm)
  let table {n k : ℕ} (hk : 0 < k) (rows : List String) : Fin n → Fin n → Fin k :=
    let values := rows.map (fun s => s.toList.map (fun ch =>
      let c := ch.toNat
      (⟨(if c < 58 then c - 48 else c - 87) % k, Nat.mod_lt _ hk⟩ : Fin k)))
    fun i j => (values.getD i.val []).getD j.val ⟨0,hk⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hexception
  rcases hexception with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine liftCert (by decide) (by decide) (table (by decide) ["244553","522336","522336","600114","600114","560014"]) (fun x => table (by decide) ["001122","001122","334455","334455","667788","666777"] x.1 x.2) ?_ ?_ ?_ ?_ <;> set_option maxRecDepth 100000 in decide +kernel
  · refine liftCert (by decide) (by decide) (table (by decide) ["2221113","4330005","4112200","4112200","6556666","6334455","6334455"]) (fun x => table (by decide) ["0011233","0011233","0011223","4455667","4455667","4455667","8899aab"] x.1 x.2) ?_ ?_ ?_ ?_ <;> set_option maxRecDepth 100000 in decide +kernel
  · refine liftCert (by decide) (by decide) (table (by decide) ["5600711","2300711","2300711","4722833","4722833","4455866","8455866"]) (fun x => table (by decide) ["0001112","0001112","3334445","3334445","6667778","9667778","999aaab"] x.1 x.2) ?_ ?_ ?_ ?_ <;> set_option maxRecDepth 100000 in decide +kernel
  · refine liftCert (by decide) (by decide) (table (by decide) ["4400084","5440088","1556677","1556677","1118822","3339922","6339927"]) (fun x => table (by decide) ["0112333","0011223","0011223","4455667","8455667","845566a","8899aaa"] x.1 x.2) ?_ ?_ ?_ ?_ <;> set_option maxRecDepth 100000 in decide +kernel
  · refine liftCert (by decide) (by decide) (table (by decide) ["1277377","8811922","8811922","0933a44","0933a44","0055a66","4055a66"]) (fun x => table (by decide) ["0001112","0001112","3334445","3334445","6667778","9667778","999aaab"] x.1 x.2) ?_ ?_ ?_ ?_ <;> set_option maxRecDepth 100000 in decide +kernel
  · refine liftCert (by decide) (by decide) (table (by decide) ["23229334","52299336","94455660","94455660","7aaaa000","b7788111","b7788118","abbccccb"]) (fun x => table (by decide) ["00011133","00112233","00112233","44556677","4455667b","4455667b","8899aabb","8899aabb"] x.1 x.2) ?_ ?_ ?_ ?_ <;> set_option maxRecDepth 100000 in decide +kernel
  · refine liftCert (by decide) (by decide) (table (by decide) ["120034456","551151156","551151156","662262204","662262204","773370004","773370078","783384488","783384488"]) (fun x => table (by decide) ["000111222","000111222","333444555","333444555","666777888","6667778bb","999aaabbb","999aaabbb","cccdddeee"] x.1 x.2) ?_ ?_ ?_ ?_ <;> set_option maxRecDepth 100000 in decide +kernel
  · refine liftCert (by decide) (by decide) (table (by decide) ["564475589","a40050056","440050056","461161177","461161177","782282289","782282289","9933a33aa","9933a33aa"]) (fun x => table (by decide) ["000111222","000111222","033444555","333444555","666777888","666777888","999aaabbb","999aaabbb","cccdddeee"] x.1 x.2) ?_ ?_ ?_ ?_ <;> set_option maxRecDepth 100000 in decide +kernel
  · refine liftCert (by decide) (by decide) (table (by decide) ["234005622","345116722","345116722","899339a44","899339a44","10a55ab66","10a55ab66","10077bb88","78077bb88"]) (fun x => table (by decide) ["000011112","000011112","333344445","333344445","666677778","666677778","9999aaaab","cc99aaaab","ccccdddde"] x.1 x.2) ?_ ?_ ?_ ?_ <;> set_option maxRecDepth 100000 in decide +kernel
  · refine liftCert (by decide) (by decide) (table (by decide) ["78a00bc11","234005911","234005911","aab22bc33","aab22bc33","96c44dd55","96c44dd55","96677ee88","de677ee88"]) (fun x => table (by decide) ["000011112","000011112","333344445","333344445","666677778","666677778","9999aaaab","cc99aaaab","ccccdddde"] x.1 x.2) ?_ ?_ ?_ ?_ <;> set_option maxRecDepth 100000 in decide +kernel
  · refine liftCert (by decide) (by decide) (table (by decide) ["511167222","8001122bb","b00556677","b00556677","9ccccdddd","e8899aa33","e8899aa33","aee44ffb3","c444dffef"]) (fun x => table (by decide) ["001222234","001122334","001122334","556677889","556677889","556677889","aabbccdde","aabbccddd","aabcccddd"] x.1 x.2) ?_ ?_ ?_ ?_ <;> set_option maxRecDepth 100000 in decide +kernel
  · refine liftCert (by decide) (by decide) (table (by decide) ["34aa5aa67","0b33b44cc","0b33b44cc","0055d66d1","8055d66d1","ee77f8811","ee77f8819","ab22f99gg","c222f99gg"]) (fun x => table (by decide) ["000111222","000111222","333444555","633444555","666777888","66677788b","999aaabbb","999aaabbb","99cdddeee"] x.1 x.2) ?_ ?_ ?_ ?_ <;> set_option maxRecDepth 100000 in decide +kernel
  · refine liftCert (by decide) (by decide) (table (by decide) ["1238845aa","abb11cc22","abb11cc22","dde33ef44","dde33ef44","80f55gg66","80f55gg66","80077hh99","67077hh99"]) (fun x => table (by decide) ["000011112","000011112","333344445","333344445","666677778","666677778","9999aaaab","cc99aaaab","ccccdddde"] x.1 x.2) ?_ ?_ ?_ ?_ <;> set_option maxRecDepth 100000 in decide +kernel
  · refine liftCert (by decide) (by decide) (table (by decide) ["23aa40005a","67bb8009aa","bc22c33d44","bc22c33d44","bcdddeeeee","ff55g66g77","ff55g66g77","fghhhhhi11","ii88j99j11","ii88j99j1j"]) (fun x => table (by decide) ["0001113222","0001112223","0001112223","4445556667","4445556667","4445556667","888999aaab","888999aaab","888999aaae","cccdddeeee"] x.1 x.2) ?_ ?_ ?_ ?_ <;> set_option maxRecDepth 100000 in decide +kernel

