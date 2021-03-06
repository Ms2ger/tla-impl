use std::collections::BTreeMap;
use std::rc::Rc;
use std::cell::RefCell;
use std::fmt::Debug;

#[derive(Clone, Debug)]
struct LoudVec<T>(Vec<T>, String);

impl<T: Debug> LoudVec<T> {
  fn new(name: impl Into<String>) -> Self {
    Self(vec![], name.into())
  }
  fn push(&mut self, value: T) {
    print!("{}: Push {:?}; ", self.1, value);
    self.0.push(value);
    println!("vector is now {:?}", self.0);
  }
  fn pop(&mut self) -> Option<T> {
    let value = self.0.pop();
    println!("{}: Pop {:?}; vector is now {:?}", self.1, value, self.0);
    value
  }
}

impl<T> ::std::ops::Deref for LoudVec<T> {
  type Target = Vec<T>;
  fn deref(&self) -> &Self::Target {
    &self.0
  }
}

impl<T> ::std::ops::DerefMut for LoudVec<T> {
  fn deref_mut(&mut self) -> &mut Self::Target {
    &mut self.0
  }
}

impl<T> IntoIterator for LoudVec<T> {
  type Item = T;
  type IntoIter = <Vec<T> as IntoIterator>::IntoIter;
  fn into_iter(self) -> Self::IntoIter {
    self.0.into_iter()
  }
}

struct Promise {
  data: RefCell<Option<Result<(), String>>>,
  children: RefCell<Vec<(Box<dyn FnOnce(&mut Modules)>, Box<dyn FnOnce(&mut Modules, String)>)>>,
}

impl Promise {
  fn new(modules: &mut Modules) -> Rc<Self> {
    let result = Rc::new(Self {
      data: RefCell::new(None),
      children: RefCell::new(Vec::new()),
    });
    modules.record(result.clone());
    result
  }
  fn resolve(&self) {
    let mut cell = self.data.borrow_mut();
    assert_eq!(*cell, None);
    *cell = Some(Ok(()));
  }
  fn reject(&self, error: String) {
    let mut cell = self.data.borrow_mut();
    assert_eq!(*cell, None);
    *cell = Some(Err(error));
  }
  fn then(&self, resolve: Box<dyn FnOnce(&mut Modules)>, reject: Box<dyn FnOnce(&mut Modules, String)>) {
    let mut children = self.children.borrow_mut();
    children.push((resolve, reject));
  }
  fn tick(&self, modules: &mut Modules) {
    if let Some(result) = &*self.data.borrow() {
      println!("Tick: result={:?}, calling {} children", result, self.children.borrow().len());
      for (resolve, reject) in self.children.borrow_mut().drain(..) {
        match result {
          Ok(()) => resolve(modules),
          Err(e) => reject(modules, e.clone()),
        }
      }
    }
  }
}

impl std::fmt::Debug for Promise {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
    "Promise".fmt(f)
  }
}

#[derive(PartialOrd, Ord, PartialEq, Eq, Debug, Copy, Clone)]
enum Sync {
  Sync,
  Async,
}

#[derive(PartialOrd, Ord, PartialEq, Eq, Debug)]
enum Status {
  Unlinked,
  Linking,
  Linked,
  Evaluating,
  Evaluated,
}

#[derive(Debug)]
struct Module {
  name: String,
  broken: bool,

  status: Status,
  error: Option<String>,
  dfs_index : Option<usize>,
  dfs_anc_index: Option<usize>,
  requested: Vec<String>,
  async_: Sync,
  async_evaluating: bool,
  apm: Option<LoudVec<String>>,
  pad: Option<usize>,

  promise: Option<Rc<Promise>>
}

#[derive(Debug)]
enum EvalResult {
  Index(usize),
  Error(String),
}


impl Module {
  fn new(name: String, async_: Sync, requested: Vec<String>, broken: bool) -> Self {
    Module {
      name,
      broken,

      status: Status::Unlinked,
      error: None,
      dfs_index: None,
      dfs_anc_index: None,
      requested,
      async_,
      async_evaluating: false,
      apm: None,
      pad: None,

      promise: None,
    }
  }
  fn set_status(&mut self, status: Status) {
    println!("Setting {} status from {:?} to {:?}", self.name, self.status, status);
    assert!(status > self.status);
    self.status = status;
  }
  fn set_anc_index(&mut self, dfs_anc_index: usize) {
    println!("Setting [[DFSAncestorIndex]] for {} from {:?} to {}", self.name, self.dfs_anc_index, dfs_anc_index);
    self.dfs_anc_index = Some(dfs_anc_index);
  }

  fn execute_module_sync(&self) -> Result<(), String> {
    println!("execute_module_sync: {}", self.name);
    assert_eq!(self.async_, Sync::Sync);
    if self.broken {
      Err(format!("Module {} failed sync", self.name))
    } else {
      Ok(())
    }
  }
  fn execute_module_async(&self, capability: Rc<Promise>) {
    println!("execute_module_async: {}", self.name);
    assert_eq!(self.async_, Sync::Async);
    if self.broken {
      capability.reject(format!("Module {} failed async", self.name));
    } else {
      capability.resolve();
    }
  }
}

struct Modules {
  modules: BTreeMap<String, Module>,
  execution_order: Vec<String>,
  promises: Vec<Rc<Promise>>,
}

impl Modules {
  fn new() -> Self {
    Modules {
      modules: BTreeMap::new(),
      execution_order: Vec::new(),
      promises: Vec::new(),
    }
  }

  fn record(&mut self, promise: Rc<Promise>) {
    self.promises.push(promise);
  }

  fn tick(&mut self) {
    for promise in self.promises.clone() {
      promise.tick(self);
    }
  }

  fn get(&self, name: &str) -> &Module {
    self.modules.get(name).unwrap()
  }

  fn get_mut(&mut self, name: &str) -> &mut Module {
    self.modules.get_mut(name).unwrap()
  }

  fn insert(&mut self, name: String, async_: Sync, requested: Vec<String>, broken: bool) {
    self.modules.insert(name.clone(), Module::new(name, async_, requested, broken));
  }

  fn cycle_root(&self, module: &str) -> String {
    println!("Fetching cycle root of {}", module);
    assert_eq!(self.get(module).status, Status::Evaluated);
    let mut module = module.to_owned();
    if self.get(&module).apm.as_ref().unwrap().is_empty() {
      return module;
    }

    while self.get(&module).dfs_index.unwrap() > self.get(&module).dfs_anc_index.unwrap() {
      assert!(!self.get(&module).apm.as_ref().unwrap().is_empty(), "APM for {} is empty", module);
      let next = self.get(&module).apm.as_ref().unwrap()[0].to_owned();
      assert!(self.get(&next).dfs_anc_index.unwrap() <= self.get(&module).dfs_anc_index.unwrap());
      module = next;
      println!("    >> {}", module);
    }
    assert_eq!(self.get(&module).dfs_index, self.get(&module).dfs_anc_index);
    println!("    result={}", module);
    module
  }

  fn inner_module_linking(&mut self, name: &str, stack: &mut LoudVec<String>, index: usize) -> usize {
    match &self.get(name).status {
      // Step 2.
      | s @ Status::Linking
      | s @ Status::Linked
      | s @ Status::Evaluated
      => {
        println!("inner_module_linking: short circuit for {} with {:?}", name, s);
        return index;
      },
      // Step 3.
      | Status::Unlinked
      => (),
      | s
      => panic!("Wrong status for {}: {:?}", name, s),
    };
    // Step 4.
    self.get_mut(name).set_status(Status::Linking);
    // Step 5.
    self.get_mut(name).dfs_index = Some(index);
    // Step 6.
    self.get_mut(name).set_anc_index(index);
    // Step 7.
    let mut index = index + 1;
    // Step 8.
    stack.push(name.to_owned());
    // Step 9.
    for required in self.get(name).requested.clone() {
      index = self.inner_module_linking(&required, stack, index);
      match &self.get(&required).status {
        | Status::Linking
        => {
          assert!(stack.contains(&required));
          let dfs_anc_index = self.get(name).dfs_anc_index.unwrap().min(self.get(&required).dfs_anc_index.unwrap());
          self.get_mut(name).set_anc_index(dfs_anc_index);
        },
        | Status::Linked
        | Status::Evaluated
        => {
          assert!(!stack.contains(&required));
        },
        | s
        => panic!("Wrong status for {}: {:?}", required, s),
      };

      if self.get(&required).async_ == Sync::Async {
        self.get_mut(name).async_ = Sync::Async;
      }
    }
    // Step 10.
    // Step 11.
    assert_eq!(stack.iter().filter(|s| **s == name).count(), 1);
    // Step 12.
    assert!(self.get(name).dfs_anc_index.unwrap() <=
            self.get(name).dfs_index.unwrap());
    // Step 13.
    if self.get(name).dfs_anc_index.unwrap() == self.get(name).dfs_index.unwrap() {
      let mut done = false;
      while !done {
        let required = stack.pop().unwrap();
        self.get_mut(&required).set_status(Status::Linked);
        done = required == name;
      }
    }
    // Step 14.
    index
  }

  fn link(&mut self, name: &str) {
    assert!(self.get(name).status != Status::Linking && self.get(name).status != Status::Evaluating);
    let mut stack = LoudVec::new("Link stack");
    self.inner_module_linking(name, &mut stack, 0);
    match self.get(name).status {
      | Status::Linked
      | Status::Evaluated
      => (),
      | ref s
      => panic!("Wrong status for {}: {:?}", name, s),
    }
    assert!(stack.is_empty());
  }

  fn fulfilled(&mut self, name: &str) {
    println!("Fulfilled({})", name);
    // Step 1.
    match self.get(name).status {
      | Status::Evaluated
      => (),
      | ref s
      => panic!("Wrong status for {}: {:?}", name, s),
    }

    // Step 2.
    if !self.get(name).async_evaluating {
      // XXX why?
      assert!(self.get(name).error.is_some());
      return;
    }

    // Step 3.
    assert!(self.get(name).error.is_none());

    // Step 4.
    self.get_mut(name).async_evaluating = false;

    // Step 5.
    for m in self.get(name).apm.clone().unwrap() {
      println!("  > parent module {:?}", self.get(&m));
      if self.get(name).dfs_index.unwrap() != self.get(name).dfs_anc_index.unwrap() {
        assert!(self.get(&m).dfs_anc_index.unwrap() <= self.get(name).dfs_anc_index.unwrap());
      }
      assert!(self.get(&m).pad.unwrap() > 0);
      *self.get_mut(&m).pad.as_mut().unwrap() -= 1;
      if self.get(&m).pad.unwrap() == 0 && self.get(&m).error.is_none() {
        assert!(self.get(&m).async_evaluating);
        let root = self.cycle_root(&m);
        if self.get(&root).error.is_some() {
          return;
        }
        if self.get(&m).async_ == Sync::Async {
          self.execute_cyclic_module(&m);
        } else {
          self.execution_order.push(m.to_owned());
          let result = self.get(&m).execute_module_sync();
          match result {
            Ok(()) => self.fulfilled(&m),
            Err(e) => self.rejected(&m, &e),
          }
        }
      }
    }
    if let Some(promise) = self.get(name).promise.clone() {
      assert_eq!(self.get(name).dfs_index, self.get(name).dfs_anc_index);
      promise.resolve();
    }
  }

  fn rejected(&mut self, name: &str, error: &str) {
    println!("Rejected({})", name);
    // Step 1.
    match self.get(name).status {
      | Status::Evaluated
      => (),
      | ref s
      => panic!("Wrong status for {}: {:?}", name, s),
    }

    // Step 2.
    if !self.get(name).async_evaluating {
      // XXX why?
      assert!(self.get(name).error.is_some());
      return;
    }

    // Step 3.
    assert_eq!(self.get(name).error, None);

    // Step 4.
    self.get_mut(name).error = Some(error.to_owned());

    // Step 5.
    self.get_mut(name).async_evaluating = false;

    // Step 6.
    for m in self.get(name).apm.clone().unwrap() {
      if self.get(name).dfs_index.unwrap() != self.get(name).dfs_anc_index.unwrap() {
        assert_eq!(self.get(&m).dfs_anc_index.unwrap(), self.get(name).dfs_anc_index.unwrap());
      }
      self.rejected(&m, error);
    }

    if let Some(promise) = self.get(name).promise.clone() {
      assert_eq!(self.get(name).dfs_index, self.get(name).dfs_anc_index);
      promise.reject(error.to_owned());
    }
  }

  fn execute_cyclic_module(&mut self, name: &str) {
    println!("Execute cyclic module: {}", name);
    match &self.get(name).status {
      | Status::Evaluating
      | Status::Evaluated
      => (),
      | s
      => panic!("Wrong status for {}: {:?}", name, s),
    }

    self.get_mut(name).async_evaluating = true;

    self.execution_order.push(name.to_owned());
    if self.get(name).async_ == Sync::Sync {
      let result = self.get(name).execute_module_sync();
      match result {
        Ok(()) => self.fulfilled(name),
        Err(e) => self.rejected(name, &e),
      }
    } else {
      let capability = Promise::new(self);
      let name1 = name.to_owned();
      let name2 = name.to_owned();
      capability.then(
        Box::new(move |modules| modules.fulfilled(&name1)),
        Box::new(move |modules, error| modules.rejected(&name2, &error)),
      );
      self.get(name).execute_module_async(capability.clone());
    }
  }


  fn inner_module_evaluation(&mut self, name: &str, stack: &mut LoudVec<String>, index: usize) -> EvalResult {
    match &self.get(name).status {
      // Step 2.
      | Status::Evaluated
      => {
        return match &self.get(name).error {
          Some(error) => EvalResult::Error(error.clone()),
          None => EvalResult::Index(index)
        };
      },
      // Step 3.
      | Status::Evaluating
      => return EvalResult::Index(index),
      // Step 4.
      | Status::Linked
      => (),
      | s
      => panic!("Wrong status for {}: {:?}", name, s),
    }
    // Step 5.
    self.get_mut(name).set_status(Status::Evaluating);

    // Step 6.
    self.get_mut(name).dfs_index = Some(index);
    // Step 7.
    self.get_mut(name).set_anc_index(index);

    // Step 8.
    self.get_mut(name).pad = Some(0);
    // Step 9.
    self.get_mut(name).apm = Some(LoudVec::new(format!("{}.[[AsyncParentModules]]", name)));
    // Step 10.
    let mut index = index + 1;
    // Step 11.
    stack.push(name.to_owned());
    
    // Step 12.
    for required in self.get(name).requested.clone() {
      index = match self.inner_module_evaluation(&required, stack, index) {
        EvalResult::Error(error) => return EvalResult::Error(error),
        EvalResult::Index(index) => index,
      };

      let required = match &self.get(&required).status {
        | Status::Evaluating
        => {
          assert!(stack.contains(&required));
          let dfs_anc_index = self.get(name).dfs_anc_index.unwrap().min(self.get(&required).dfs_anc_index.unwrap());
          self.get_mut(name).set_anc_index(dfs_anc_index);
          required
        },
        | Status::Evaluated
        => {
          assert!(!stack.contains(&required));
          let root = self.cycle_root(&required);
          assert_eq!(self.get(&root).status, Status::Evaluated);
          if let Some(error) = &self.get(&required).error {
            return EvalResult::Error(error.clone());
          }
         root
        },
        | s
        => panic!("Wrong status for {}: {:?}", required, s),
      };

      println!("Considering registering async dependency {} -> {}", name, required);
      println!("    module = {:?}", self.get(&name));
      println!("    required = {:?}", self.get(&required));
      if self.get(&required).async_evaluating {
        *self.get_mut(name).pad.as_mut().unwrap() += 1;
        self.get_mut(&required).apm.as_mut().unwrap().push(name.to_owned());
      }
    }

    // Step 14
    println!("{}.PAD = {}", name, self.get(&name).pad.unwrap());
    if self.get(&name).pad.unwrap() > 0 {
      self.get_mut(&name).async_evaluating = true;
    } else if self.get(&name).async_ == Sync::Async {
      self.execute_cyclic_module(name);
    } else {
      self.execution_order.push(name.to_owned());
      let result = self.get(name).execute_module_sync();
      match result {
        Ok(()) => (),
        Err(e) => return EvalResult::Error(e),
      }
    }

    // Step 15.
    assert_eq!(stack.iter().filter(|s| **s == name).count(), 1);
    // Step 16.
    assert!(self.get(name).dfs_anc_index.unwrap() <=
            self.get(name).dfs_index.unwrap());
    // Step 17.
    if self.get(name).dfs_anc_index.unwrap() == self.get(name).dfs_index.unwrap() {
      let mut done = false;
      while !done {
        let required = stack.pop().unwrap();
        self.get_mut(&required).set_status(Status::Evaluated);
        done = required == name;
      }
    }

    // Step 18.
    EvalResult::Index(index)
  }

  fn evaluate(&mut self, name: &str) -> Rc<Promise> {
    let name = match &self.get(name).status {
      | Status::Linked
      => name.to_owned(),
      // Step 3.
      | Status::Evaluated
      => self.cycle_root(name),
      // Step 2.
      | s
      => panic!("Wrong status for {}: {:?}", name, s),
    };

    // Step 4.
    if let Some(promise) = self.get(&name).promise.clone() {
      return promise;
    }

    // Step 5.
    let mut stack = LoudVec::new("Evaluate stack");

    // Step 6.
    let promise = Promise::new(self);

    // Step 7.
    self.get_mut(&name).promise = Some(promise.clone());

    // Step 8.
    let result = self.inner_module_evaluation(&name, &mut stack, 0);
    println!("Result for {}: {:?}", name, result);

    match result {
      // Step 9.
      EvalResult::Error(e) => {
        println!("Found error with stack {:?}", stack);
        for m in stack.iter() {
          assert_eq!(self.get(&m).status, Status::Evaluating);
          self.get_mut(&m).set_status(Status::Evaluated);
          match &self.get(&m).error {
            Some(err) => assert_eq!(err, &e),
            None => (),
          }
          self.get_mut(&m).error = Some(e.clone());
        }
        let r = promise.data.borrow().is_none();
        if r {
          promise.reject(e.clone());
        }
        assert_eq!(self.get(&name).status, Status::Evaluated);
        assert!(self.get(&name).error.is_some());
        assert_eq!(*self.get(&name).error.as_ref().unwrap(), e);
      },
      // Step 10.
      EvalResult::Index(_) => {
        assert!(self.get(&name).status == Status::Evaluated);
        assert!(self.get(&name).error.is_none());
        assert!(stack.is_empty());
        if !self.get(&name).async_evaluating {
          promise.resolve();
        }
      },
    }

    // Step 11.
    promise
  }
}

fn run(modules: &mut Modules, name: &str) -> Rc<Promise> {
  println!(">>> Link");
  modules.link(name);
  for (k, v) in &mut modules.modules {
    println!("Module {}: DFSIndex={:?} DFSAncestorIndex={:?} Async={:?}", k, v.dfs_index, v.dfs_anc_index, v.async_);
  }

  println!(">>> Evaluate");
  let promise = modules.evaluate(name);
  for (k, v) in &modules.modules {
    assert_ne!(v.status, Status::Evaluating, "{}", k);
    println!("{:?}", v);
  }
  println!("=================");
  promise
}

#[cfg(test)]
fn check(modules: &mut Modules, expected: &[(&[&str], &[&str])]) {
  let mut all_started: Vec<&str> = vec![];
  let mut all_finished: Vec<&str> = vec![];
  for (started, finished) in expected {
    all_started.extend(*started);
    all_finished.extend(*finished);
    assert_eq!(modules.execution_order, all_started);
    for m in modules.modules.values() {
      assert_eq!(m.async_evaluating, !all_finished.contains(&&*m.name));
      assert_eq!(m.status, Status::Evaluated);
      assert!(m.error.is_none());
    }
    modules.tick();
  }
}

#[test]
fn example1() {
  println!("Example 1");
  let mut modules = Modules::new();
  modules.insert("A".to_owned(), Sync::Async, vec!["B".to_owned(), "C".to_owned()], false);
  modules.insert("B".to_owned(), Sync::Async, vec!["A".to_owned(), "D".to_owned(), "E".to_owned()], false);
  modules.insert("C".to_owned(), Sync::Async, vec![], false);
  modules.insert("D".to_owned(), Sync::Async, vec![], false);
  modules.insert("E".to_owned(), Sync::Async, vec![], false);
  run(&mut modules, "A");

  let expected: &[(&[&str], &[&str])] = &[
    (&["D", "E", "C"], &[]),
    (&["B"], &["D", "E", "C"]),
    (&["A"], &["B"]),
    (&[], &["A"]),
  ];
  check(&mut modules, expected);
}

#[test]
fn example2() {
  println!("Example 2");
  let mut modules = Modules::new();
  modules.insert("A".to_owned(), Sync::Async, vec!["B".to_owned(), "C".to_owned()], false);
  modules.insert("B".to_owned(), Sync::Async, vec!["A".to_owned()], false);
  modules.insert("C".to_owned(), Sync::Sync, vec![], false);
  run(&mut modules, "A");

  let expected: &[(&[&str], &[&str])] = &[
    (&["B", "C"], &["C"]),
    (&["A"], &["B"]),
    (&[], &["A"]),
  ];
  check(&mut modules, expected);
}

#[test]
fn example2b() {
  println!("Example 2");
  let mut modules = Modules::new();
  modules.insert("A".to_owned(), Sync::Async, vec!["B".to_owned()], false);
  modules.insert("B".to_owned(), Sync::Async, vec!["A".to_owned(), "C".to_owned()], false);
  modules.insert("C".to_owned(), Sync::Sync, vec![], false);
  run(&mut modules, "A");

  let expected: &[(&[&str], &[&str])] = &[
    (&["C", "B"], &["C"]),
    (&["A"], &["B"]),
    (&[], &["A"]),
  ];
  check(&mut modules, expected);
}

#[test]
fn example3() {
  println!("Example 3");
  let mut modules = Modules::new();
  modules.insert("B".to_owned(), Sync::Sync, vec![], true);
  run(&mut modules, "B");
}

#[test]
fn example4() {
  println!("Example 4");
  let mut modules = Modules::new();
//  modules.insert("A".to_owned(), Sync::Async, vec!["B".to_owned(), "C".to_owned(), "D".to_owned()], false);
//  modules.insert("A".to_owned(), Sync::Async, vec!["B".to_owned()], false);
  modules.insert("B".to_owned(), Sync::Async, vec!["C".to_owned()], false);
//  modules.insert("B".to_owned(), Sync::Sync, vec!["C".to_owned()], false);
  modules.insert("C".to_owned(), Sync::Sync, vec![], true);
//  modules.insert("D".to_owned(), Sync::Sync, vec![], false);
  run(&mut modules, "B");
  modules.evaluate("B");
//  modules.evaluate("C");
//  modules.evaluate("D");
}

#[test]
fn example5() {
  let mut modules = Modules::new();
  modules.insert("A".to_owned(), Sync::Async, vec!["B".to_owned(), "C".to_owned()], false);
  modules.insert("B".to_owned(), Sync::Async, vec!["D".to_owned()], false);
  modules.insert("C".to_owned(), Sync::Async, vec!["D".to_owned()], false);
  modules.insert("D".to_owned(), Sync::Async, vec![], false);
  run(&mut modules, "A");

  let expected: &[(&[&str], &[&str])] = &[
    (&["D"], &[]),
    (&["B", "C"], &["D"]),
    (&["A"], &["B", "C"]),
    (&[], &["A"]),
  ];
  check(&mut modules, expected);
}

#[test]
fn example6() {
  let mut modules = Modules::new();
  modules.insert("A".to_owned(), Sync::Async, vec!["B".to_owned()], false);
  modules.insert("B".to_owned(), Sync::Async, vec!["A".to_owned()], false);
  run(&mut modules, "A");

  let expected: &[(&[&str], &[&str])] = &[
    (&["B"], &[]),
    (&["A"], &["B"]),
    (&[], &["A"]),
  ];
  check(&mut modules, expected);
}

#[test]
fn example7() {
  let mut modules = Modules::new();
  modules.insert("A".to_owned(), Sync::Async, vec!["B".to_owned()], false);
  modules.insert("B".to_owned(), Sync::Async, vec!["A".to_owned(), "C".to_owned()], false);
  modules.insert("C".to_owned(), Sync::Async, vec![], false);
  run(&mut modules, "A");

  let expected: &[(&[&str], &[&str])] = &[
    (&["C"], &[]),
    (&["B"], &["C"]),
    (&["A"], &["B"]),
    (&[], &["A"]),
  ];
  check(&mut modules, expected);
}

#[test]
fn example_single_broken_sync() {
  let mut modules = Modules::new();
  modules.insert("A".to_owned(), Sync::Sync, vec![], true);
  run(&mut modules, "A");
  assert_eq!(modules.execution_order, &[
    "A".to_owned(),
  ]);
  for m in modules.modules.values() {
    assert_eq!(m.status, Status::Evaluated);
    assert!(m.error.is_some());
  }
}

#[test]
fn example_single_broken_async() {
  let mut modules = Modules::new();
  modules.insert("A".to_owned(), Sync::Async, vec![], true);
  run(&mut modules, "A");
  assert_eq!(modules.execution_order, &[
    "A".to_owned(),
  ]);
  for m in modules.modules.values() {
    assert_eq!(m.status, Status::Evaluated);
    assert!(m.error.is_none());
  }

  modules.tick();
  for m in modules.modules.values() {
    assert_eq!(m.status, Status::Evaluated);
    assert!(m.error.is_some());
  }
}

#[test]
fn example_guy() {
  println!("Example Guy");
  let mut modules = Modules::new();
  modules.insert("A".to_owned(), Sync::Async, vec!["B".to_owned(), "C".to_owned()], false);
  modules.insert("B".to_owned(), Sync::Async, vec!["D".to_owned()], false);
  modules.insert("C".to_owned(), Sync::Async, vec!["D".to_owned(), "E".to_owned()], false);
  modules.insert("D".to_owned(), Sync::Async, vec!["A".to_owned()], false);
  modules.insert("E".to_owned(), Sync::Async, vec![], false);
  run(&mut modules, "A");

  let expected: &[(&[&str], &[&str])] = &[
    (&["D", "E"], &[]),
    (&["B", "C"], &["D", "E"]),
    (&["A"], &["B", "C"]),
    (&[], &["A"]),
  ];
  check(&mut modules, expected);
}

#[test]
fn example_common_dep() {
  let mut modules = Modules::new();
  modules.insert("A".to_owned(), Sync::Async, vec!["B".to_owned(), "C".to_owned()], false);
  modules.insert("B".to_owned(), Sync::Async, vec!["D".to_owned()], false);
  modules.insert("C".to_owned(), Sync::Async, vec!["D".to_owned()], false);
  modules.insert("D".to_owned(), Sync::Async, vec![], false);
  run(&mut modules, "A");

  let expected: &[(&[&str], &[&str])] = &[
    (&["D"], &[]),
    (&["B", "C"], &["D"]),
    (&["A"], &["B", "C"]),
    (&[], &["A"]),
  ];
  check(&mut modules, expected);
}

#[test]
fn example_common_dep_cycle() {
  let mut modules = Modules::new();
  modules.insert("A".to_owned(), Sync::Async, vec!["B".to_owned(), "C".to_owned()], false);
  modules.insert("B".to_owned(), Sync::Async, vec!["D".to_owned()], false);
  modules.insert("C".to_owned(), Sync::Async, vec!["D".to_owned()], false);
  modules.insert("D".to_owned(), Sync::Async, vec!["A".to_owned()], false);
  run(&mut modules, "A");

  let expected: &[(&[&str], &[&str])] = &[
    (&["D"], &[]),
    (&["B", "C"], &["D"]),
    (&["A"], &["B", "C"]),
    (&[], &["A"]),
  ];
  check(&mut modules, expected);
}

#[test]
fn example_common_dep_cycle_2() {
  let mut modules = Modules::new();
  modules.insert("A".to_owned(), Sync::Async, vec!["B".to_owned(), "C".to_owned()], false);
  modules.insert("B".to_owned(), Sync::Async, vec!["D".to_owned()], false);
  modules.insert("C".to_owned(), Sync::Async, vec!["D".to_owned()], false);
  modules.insert("D".to_owned(), Sync::Async, vec!["A".to_owned(), "F".to_owned()], false);
  modules.insert("F".to_owned(), Sync::Async, vec![], false);
  run(&mut modules, "A");

  let expected: &[(&[&str], &[&str])] = &[
    (&["F"], &[]),
    (&["D"], &["F"]),
    (&["B", "C"], &["D"]),
    (&["A"], &["B", "C"]),
    (&[], &["A"]),
  ];
  check(&mut modules, expected);
}

#[test]
fn example_common_dep_cycle_2b() {
  let mut modules = Modules::new();
  modules.insert("A".to_owned(), Sync::Async, vec!["B".to_owned(), "C".to_owned()], false);
  modules.insert("B".to_owned(), Sync::Async, vec!["D".to_owned()], false);
  modules.insert("C".to_owned(), Sync::Async, vec!["D".to_owned()], false);
  modules.insert("D".to_owned(), Sync::Async, vec!["A".to_owned(), "F".to_owned()], false);
  modules.insert("F".to_owned(), Sync::Async, vec![], false);
  run(&mut modules, "F");

  assert_eq!(modules.execution_order, &[
    "F".to_owned(),
  ]);
  assert_eq!(modules.modules["F"].status, Status::Evaluated);
  assert!(modules.modules["F"].async_evaluating);
  modules.tick();
  assert_eq!(modules.modules["F"].status, Status::Evaluated);
  assert!(!modules.modules["F"].async_evaluating);

  run(&mut modules, "A");

  let expected: &[(&[&str], &[&str])] = &[
    (&["F", "D"], &["F"]),
    (&["B", "C"], &["D"]),
    (&["A"], &["B", "C"]),
    (&[], &["A"]),
  ];
  check(&mut modules, expected);
}

#[test]
fn example_common_dep_cycle_2c() {
  let mut modules = Modules::new();
  modules.insert("A".to_owned(), Sync::Async, vec!["B".to_owned(), "C".to_owned()], false);
  modules.insert("B".to_owned(), Sync::Async, vec!["D".to_owned()], false);
  modules.insert("C".to_owned(), Sync::Async, vec!["D".to_owned()], false);
  modules.insert("D".to_owned(), Sync::Async, vec!["A".to_owned(), "F".to_owned()], false);
  modules.insert("F".to_owned(), Sync::Async, vec![], false);
  run(&mut modules, "F");
  assert_eq!(modules.execution_order, &[
    "F".to_owned(),
  ]);
  assert_eq!(modules.modules["F"].status, Status::Evaluated);
  assert!(modules.modules["F"].async_evaluating);

  run(&mut modules, "A");

  let expected: &[(&[&str], &[&str])] = &[
    (&["F"], &[]),
    (&["D"], &["F"]),
    (&["B", "C"], &["D"]),
    (&["A"], &["B", "C"]),
    (&[], &["A"]),
  ];
  check(&mut modules, expected);
}

#[test]
fn example_common_dep_cycle_2d() {
  let mut modules = Modules::new();
  modules.insert("E".to_owned(), Sync::Async, vec!["A".to_owned()], false);
  modules.insert("A".to_owned(), Sync::Async, vec!["B".to_owned(), "C".to_owned()], false);
  modules.insert("B".to_owned(), Sync::Async, vec!["D".to_owned()], false);
  modules.insert("C".to_owned(), Sync::Async, vec!["D".to_owned()], false);
  modules.insert("D".to_owned(), Sync::Async, vec!["A".to_owned(), "F".to_owned()], false);
  modules.insert("F".to_owned(), Sync::Async, vec![], false);
  run(&mut modules, "F");
  assert_eq!(modules.execution_order, &[
    "F".to_owned(),
  ]);
  assert_eq!(modules.modules["F"].status, Status::Evaluated);
  assert!(modules.modules["F"].async_evaluating);

  run(&mut modules, "E");

  let expected: &[(&[&str], &[&str])] = &[
    (&["F"], &[]),
    (&["D"], &["F"]),
    (&["B", "C"], &["D"]),
    (&["A"], &["B", "C"]),
    (&["E"], &["A"]),
    (&[], &["E"]),
  ];
  check(&mut modules, expected);
}

#[test]
fn example_common_dep_cycle_3() {
  let mut modules = Modules::new();
  modules.insert("E".to_owned(), Sync::Async, vec!["A".to_owned()], false);
  modules.insert("A".to_owned(), Sync::Async, vec!["B".to_owned(), "C".to_owned()], false);
  modules.insert("B".to_owned(), Sync::Async, vec!["D".to_owned()], false);
  modules.insert("C".to_owned(), Sync::Async, vec!["D".to_owned()], false);
  modules.insert("D".to_owned(), Sync::Async, vec!["A".to_owned(), "F".to_owned()], false);
  modules.insert("F".to_owned(), Sync::Async, vec![], false);
  run(&mut modules, "E");

  let expected: &[(&[&str], &[&str])] = &[
    (&["F"], &[]),
    (&["D"], &["F"]),
    (&["B", "C"], &["D"]),
    (&["A"], &["B", "C"]),
    (&["E"], &["A"]),
    (&[], &["E"]),
  ];
  check(&mut modules, expected);
}

#[test]
fn spec_example_1() {
  let mut modules = Modules::new();
  modules.insert("A".to_owned(), Sync::Sync, vec!["B".to_owned()], false);
  modules.insert("B".to_owned(), Sync::Sync, vec!["C".to_owned()], false);
  modules.insert("C".to_owned(), Sync::Sync, vec![], false);
  let promise = run(&mut modules, "A");
  assert!(promise.data.borrow().as_ref().unwrap().is_ok());

  let expected: &[(&[&str], &[&str])] = &[
    (&["C", "B", "A"], &["C", "B", "A"]),
    (&[], &[]),
  ];
  check(&mut modules, expected);
}

#[test]
fn spec_example_2() {
  let mut modules = Modules::new();
  modules.insert("A".to_owned(), Sync::Sync, vec!["B".to_owned()], false);
  modules.insert("B".to_owned(), Sync::Sync, vec!["C".to_owned()], true);
  modules.insert("C".to_owned(), Sync::Sync, vec![], false);
  let promise = run(&mut modules, "A");
  assert!(promise.data.borrow().as_ref().unwrap().is_err());
  assert_eq!(modules.execution_order, &[
    "C".to_owned(),
    "B".to_owned(),
  ]);
  for m in modules.modules.values() {
    assert_eq!(m.status, Status::Evaluated);
    assert!(!m.async_evaluating);
    assert_eq!(m.error.is_none(), m.name == "C");
  }
}

#[test]
fn spec_example_3() {
  let mut modules = Modules::new();
  modules.insert("A".to_owned(), Sync::Sync, vec!["B".to_owned(), "C".to_owned()], false);
  modules.insert("B".to_owned(), Sync::Sync, vec!["A".to_owned()], false);
  modules.insert("C".to_owned(), Sync::Sync, vec![], false);
  run(&mut modules, "A");

  let expected: &[(&[&str], &[&str])] = &[
    (&["B", "C", "A"], &["B", "C", "A"]),
    (&[], &[]),
  ];
  check(&mut modules, expected);
}

#[test]
fn spec_example_4() {
  let mut modules = Modules::new();
  modules.insert("A".to_owned(), Sync::Sync, vec!["B".to_owned(), "C".to_owned()], true);
  modules.insert("B".to_owned(), Sync::Sync, vec!["A".to_owned()], false);
  modules.insert("C".to_owned(), Sync::Sync, vec![], false);
  run(&mut modules, "A");

  assert_eq!(modules.execution_order, &[
    "B".to_owned(),
    "C".to_owned(),
    "A".to_owned(),
  ]);
  for m in modules.modules.values() {
    assert_eq!(m.status, Status::Evaluated);
    assert!(!m.async_evaluating);
    assert_eq!(m.error.is_none(), m.name == "C");
  }
}

#[test]
fn spec_example_4_modified() {
  let mut modules = Modules::new();
  modules.insert("A".to_owned(), Sync::Sync, vec!["B".to_owned()], true);
  modules.insert("B".to_owned(), Sync::Sync, vec!["A".to_owned()], false);
  run(&mut modules, "A");

  assert_eq!(modules.execution_order, &[
    "B".to_owned(),
    "A".to_owned(),
  ]);
  for m in modules.modules.values() {
    assert_eq!(m.status, Status::Evaluated);
    assert!(!m.async_evaluating);
    assert_eq!(m.error.is_none(), m.name == "C");
  }
}

#[test]
fn example_cycle() {
  let mut modules = Modules::new();
  modules.insert("A".to_owned(), Sync::Sync, vec!["B".to_owned()], false);
  modules.insert("B".to_owned(), Sync::Async, vec![], false);
  run(&mut modules, "B");
  assert_eq!(modules.execution_order, &[
    "B".to_owned(),
  ]);
  assert_eq!(modules.modules["B"].status, Status::Evaluated);
  modules.tick();

  assert_eq!(modules.modules["B"].status, Status::Evaluated);

  modules.link("A");
  modules.evaluate("A");

  let expected: &[(&[&str], &[&str])] = &[
    (&["B", "A"], &["B"]),
    (&[], &["A"]),
  ];
  check(&mut modules, expected);
}

#[test]
fn example_super_cycle() {
  let mut modules = Modules::new();
  modules.insert("A".to_owned(), Sync::Async, vec!["B".to_owned()], false);
  modules.insert("B".to_owned(), Sync::Async, vec!["C".to_owned()], false);
  modules.insert("C".to_owned(), Sync::Async, vec!["D".to_owned(), "E".to_owned()], false);
  modules.insert("D".to_owned(), Sync::Async, vec!["F".to_owned()], false);
  modules.insert("E".to_owned(), Sync::Async, vec!["A".to_owned()], false);
  modules.insert("F".to_owned(), Sync::Async, vec!["B".to_owned()], false);
  run(&mut modules, "A");

  let expected: &[(&[&str], &[&str])] = &[
    (&["F", "E"], &[]),
    (&["D"], &["F", "E"]),
    (&["C"], &["D"]),
    (&["B"], &["C"]),
    (&["A"], &["B"]),
    (&[], &["A"]),
  ];
  assert_eq!(modules.cycle_root("F"), "A");
  check(&mut modules, expected);
}

#[test]
fn two_step() {
  let mut modules = Modules::new();
  modules.insert("A".to_owned(), Sync::Async, vec!["B".to_owned()], false);
  modules.insert("B".to_owned(), Sync::Async, vec![], false);
  run(&mut modules, "B");
  assert_eq!(modules.execution_order, &[
    "B".to_owned(),
  ]);
  assert_eq!(modules.modules["B"].status, Status::Evaluated);
  assert!(modules.modules["B"].async_evaluating);
  modules.tick();
  assert_eq!(modules.modules["B"].status, Status::Evaluated);
  assert!(!modules.modules["B"].async_evaluating);

  run(&mut modules, "A");
  assert_eq!(modules.modules["A"].status, Status::Evaluated);
  assert!(modules.modules["A"].async_evaluating);
  modules.tick();
  assert_eq!(modules.modules["A"].status, Status::Evaluated);
  assert!(!modules.modules["A"].async_evaluating);
}

#[test]
fn cycle_error_persistence() {
  let mut modules = Modules::new();
  modules.insert("A".to_owned(), Sync::Sync, vec!["B".to_owned(), "C".to_owned()], false);
  modules.insert("B".to_owned(), Sync::Async, vec!["A".to_owned()], true);
  modules.insert("C".to_owned(), Sync::Sync, vec![], true);
  run(&mut modules, "A");
  let error = modules.modules["C"].error.clone();
  assert!(error.is_some());
  for m in modules.modules.values() {
    assert_eq!(m.status, Status::Evaluated);
    assert_eq!(m.error, error);
  }
}

#[test]
fn synchronous_cycles_121() {
  let mut modules = Modules::new();
  modules.insert("Top".to_owned(), Sync::Sync, vec!["A".to_owned(), "B".to_owned()], false);
  modules.insert("A".to_owned(), Sync::Sync, vec!["B".to_owned()], false);
  modules.insert("B".to_owned(), Sync::Sync, vec!["A".to_owned()], false);
  run(&mut modules, "Top");

  let expected: &[(&[&str], &[&str])] = &[
    (&["B", "A", "Top"], &["B", "A", "Top"]),
  ];
  check(&mut modules, expected);
}

fn main() {
}
