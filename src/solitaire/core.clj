(ns solitaire.core
  (:require clojure.edn
            [clojure.algo.monads :as m]))

(defmethod print-method clojure.lang.PersistentQueue [q w] (print-method '<- w) (print-method (seq q) w) (print-method '-< w))

(def red #{:hearts :diamonds :d :h})

(defn red? [suit] (boolean (red suit)))

(def black? (complement red?))

(defn named [i]
  (if (nil? i)
    "empty space"
    (-> i name clojure.string/capitalize)))

(defn to-s [[rank suit]]
  (->> [(if (nil? rank) "an" "the") ({11 "Jack" 12 "Queen" 13 "King" 1 "Ace"} rank rank)
        (if-not (nil? rank) "of") ({:h "Hearts" :d "Diamonds" :s "Spades" :c "Clubs"} suit (named suit))]
       (remove nil?)
       (clojure.string/join " ")))

(defn card-range
  ([suit end] (card-range suit 1 end))
  ([suit] (card-range suit 13))
  ([suit begin end]
     (->> (range begin (inc end))
          (map #(vector % suit))
          vec)))

(defn peek-pop
  ([stack]
     [(peek stack) (if (seq stack) (pop stack))])
  ([stack n]
     (loop [x n
            result [[] stack]]
       (let [[_ stack] result]
         (if-let [next-item (and (> x 0) (peek stack))]
           (recur (dec x)
                  (-> result
                      (update-in [0] conj next-item)
                      (update-in [1] pop)))
           result)))))

(defn valid-card? [[rank suit :as card]]
            (and (seq card) (= (count card) 2)
                 rank (number? rank) (<= rank 13) (> rank 0)
                 (or (red? suit) (#{:c :s :clubs :spades} suit))))

(defn card [[rank suit]]
  [rank (keyword suit)])

(defn normalize [{:keys [stock foundation tableau]}]
  "Internal representation:
     :f Foundation: up to four sequences of cards
     :tableau a sequence of maps: {:h index of next hidden :s stack}
     :w Waste: a stack of cards
     :s Stock: a queue of cards
   Extra:
     :h Hidden Tableau: a sequence of up to seven (possibly nil) sequences of cards (possibly nil). Can
          be queried for cards, and remembered so that the user doens't need to repeatedly input the same
          card(s). The parameterized value in the state describes how the down-stacks are initalized."
  (letfn [(pad [n coll]
            (->> [] repeat (concat coll) (take n) vec))
          (cards [coll]
            (->> coll (partition 2) (map card)))]
    [{:foundation (->> foundation (partition 2) (map (fn [[rank suit]] (card-range suit rank))) (pad 4))
      :tableau (->> tableau (map cards) (map-indexed (fn [index col] {:stack col :hidden index})) (pad 7))
      :history []
      :waste []
      :stock (->> stock cards (into clojure.lang.PersistentQueue/EMPTY))}]))

(letfn [(move-type [& defns]
          (fn [base-state]
            (m/domonad (m/maybe-t m/sequence-m)
                       [sub-states (foundation-to-tableau base-state)
                        state (waste-cards sub-states)
                        [find-movable destinations] (partition 2 defns)
                        source (find-movable state)
                        move (destinations source state)]
                       move)))
        (orphan [{:keys [tableau] :as state}]
          (->> tableau
               (map-indexed
                (fn [index {[[rank] :as stack] :stack}]
                  (if (and rank (not= rank 13))
                    [stack (assoc-in state [:tableau index :stack] [])
                     (str "Moved orphan stack starting with " (to-s (peek stack)) " from column " (inc index))])))))
        (orphan-parent [[[top-card :as stack] pared-state desc] {:keys [tableau] :as state}]
          (let [parent? (parent-pred top-card)]
           (->> tableau
                (map-indexed
                 (fn [index column]
                   (if (parent? column)
                     (-> pared-state
                         (update-in [:tableau index :stack] into stack)
                         (update-in [:history] conj (str desc " to " (-> column :stack first to-s) " at column " (inc index))))))))))
        (obscuring-king [{:keys [tableau] :as state}]
          (->> tableau
               (map-indexed
                (fn [index {[[rank] :as stack] :stack hidden :hidden}]
                  (if (and (= rank 13) (> hidden 0))
                    [stack (assoc-in state [:tableau index :stack] [])
                     (str "Moved " (-> stack peek to-s) "'s stack from column " (inc index))])))))
        (empty-tableau [[king-stack pared-state desc] {:keys [tableau]}]
          (->> tableau
               (map-indexed
                (fn [index {:keys [stack hidden]}]
                  (if (and (= hidden 0) (empty? stack))
                    (-> pared-state
                        (assoc-in [:tableau index :stack] king-stack)
                        (update-in [:history] conj (str desc " to column " (inc index)))))))
               (drop-while nil?)
               (take 1)))
        (waste-card [{:keys [waste] :as state}]
          [(if (seq waste)
             (let [moved-card (peek waste)]
               [moved-card
                (update-in state [:waste] pop)
                (str "Moved " (to-s moved-card) " from waste")]))])
        (tableau-card [{:keys [tableau] :as state}]
          (->> tableau
               (map-indexed
                (fn [index {:keys [stack]}]
                  (if (seq stack)
                    [(peek stack) (update-in state [:tableau index :stack] pop)
                     (str "Moved " (-> stack peek to-s) " from tableau column " (inc index))])))))
        (foundation-card [{:keys [foundation] :as state}]
          (->> foundation
               (map-indexed
                (fn [index column]
                  (if (seq column)
                    [(peek column) (update-in state [:foundation index] pop)
                     (str "Moved " (-> column peek to-s) " from foundation column " (inc index))])))))
        (to-tableau [[card pared-state desc] {:keys [tableau]}]
          (let [parent? (parent-pred card)]
            (->> tableau
                 (map-indexed
                  (fn [index column]
                    (if (parent? column)
                      (-> pared-state 
                          (update-in [:tableau index :stack] conj card)
                          (update-in [:history] conj (str desc " to tableau column " (inc index))))))))))
        (to-foundation [[[rank suit :as card] pared-state desc] {:keys [foundation]}]
          (let [ace? (= rank 1)
                [parent-rank? parent-suit?] (if ace? (repeat nil?)
                                                [#(= (dec rank) %) #(= suit %)])
                parent? (fn [[rank suit]] (and (parent-rank? rank) (parent-suit? suit)))]
            (->> foundation
                 (map-indexed
                  (fn [index stack]
                    (if (parent? (peek stack))
                      (-> pared-state
                          (update-in [:foundation index] conj card)
                          (update-in [:history] conj (str desc " to foundation column " (inc index)))))))
                 (drop-while nil?)
                 (take 1))))
        (parent-pred [[rank suit]]
          (fn [{parent-stack :stack}]
            (let [[parent-rank parent-suit] (peek parent-stack)]
              (and (= (red? parent-suit) (black? suit))
                   (= parent-rank (inc rank))))))
        (stock-to-waste [state]   ; this needs to be refactored to look at all waste states ↓
          (let [[new-waste new-stock] (-> state :stock (peek-pop 3))]
            (if (seq new-waste)
              (-> state
                  (update-in [:waste] into new-waste)
                  (assoc :stock new-stock)
                  (update-in [:history] conj "Moved stock to waste"))
              (if-let [waste (-> state :waste seq)]
                (-> state
                    (update-in [:stock] into waste)
                    (assoc :waste [])
                    (update-in [:history] conj "Filled stock with waste")
                    recur)))))
        (turn-cards-fn [ask-for-cards]
          (fn [state]
            (->> (:tableau state)
                 (map-indexed
                  (fn [index {:keys [stack hidden] :as column}]
                    (if (and (empty? stack)
                             (< 0 hidden))
                      (let [card (ask-for-cards index hidden)]
                        (-> column
                            (update-in [:stack] conj card)
                            (update-in [:hidden] dec)))
                      column)))
                 vec
                 (assoc state :tableau))))]
  (defn find-moves
    ([state]
       (let [moves (apply move-type
                          orphan orphan-parent
                          obscuring-king empty-tableau
                          tableau-card to-foundation
                          (mapcat #(vector waste-card %) [to-foundation to-tableau]))]
         (->> (moves state) (remove nil?))))
    ([state query-cards]
       (let [turn-cards (turn-cards-fn query-cards)]
         (->> state find-moves (map turn-cards))))))

(defn query-hidden [col index]
  (.start (Thread. #(println "What is at column" (inc col) "card number" index "?")))
  (let [input (atom nil)]
    (while (not (valid-card? @input))
      (reset! input (->> clojure.edn/read repeatedly (take 2) card)))
    (println "Card read:" @input)
    @input))

(defn solve
  "Takes a state (including a sequence of previous states) plus a description of the current move; returns a sequence of moves or nil.
  Keys: t (tableau) sequence of seven cards, the initial showing ones (or a sequence of card sequences, if partially played)
        f (foundation) optional; sequence of four cards, the top ones showing
        w (waste) optional (defaults to empty); a sequence of cards
        s (stock) sequence of cards in the stock, nil for unknown
   ** A card is a sequence of rank, suit; where rank: int (0, 13) inclusive, suit: #{:c :d :h :s}
      e.g. [12 :s] -> Queen of Spades
   Jack -> 11
   Queen -> 12
   King -> 13
   Ace -> 1"
  [initial-state]
  (let [get-next-moves (partial find-moves (memoize query-hidden))]
   (letfn [(add-layouts [previous state]
             (conj previous (without-history state)))
           (without-history [state]
             (select-keys state [:foundation :tableau :stock :waste]))
           (winning? [state]
             (if (every? #(= 13 (count %)) (state :foundation))
               (state :history)))
           (in? [previous state]
             (previous (without-history state)))
           (iterate-previous [previous]
             [[] previous])
           (remove-duplicates [[moves previous :as current] next-move]
             (if (in? previous next-move)
               current
               [(conj moves next-move) (conj previous (without-history next-move))]))]
     (loop [[moves previous-layouts] (reduce remove-duplicates (iterate-previous #{}) (normalize initial-state))]
       (if-let [winning-moves (some winning? moves)]
         winning-moves
         (if (seq moves)
           (do
             (println "moves:" (count moves) "previous:" (count previous-layouts))
             (->> moves
                  (mapcat get-next-moves)
                  (reduce remove-duplicates (iterate-previous previous-layouts))
                  recur))))))))
