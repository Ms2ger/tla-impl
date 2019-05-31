use std::collections::HashMap;
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
  children: RefCell<Vec<(Box<FnOnce(&mut Modules)>, Box<FnOnce(&mut Modules, String)>)>>,
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
  fn then(&self, resolve: Box<FnOnce(&mut Modules)>, reject: Box<FnOnce(&mut Modules, String)>) {
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

#[derive(PartialOrd, Ord, PartialEq, Eq, Debug, Copy, Clone)]
enum Sync {
  Sync,
  Async,
}

#[derive(PartialOrd, Ord, PartialEq, Eq, Debug)]
enum Status {
  Uninstantiated,
  Instantiating,
  Instantiated,
  Evaluating,
  EvaluatingAsync,
  Evaluated,
}

struct Module {
  name: String,
  broken: bool,

  status: Status,
  error: Option<String>,
  dfs_index : Option<usize>,
  dfs_anc_index: Option<usize>,
  requested: Vec<String>,
  async_: Sync,
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

      status: Status::Uninstantiated,
      error: None,
      dfs_index: None,
      dfs_anc_index: None,
      requested,
      async_,
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
  modules: HashMap<String, Module>,
  execution_order: Vec<String>,
  promises: Vec<Rc<Promise>>,
}

impl Modules {
  fn new() -> Self {
    Modules {
      modules: HashMap::new(),
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
    let mut module = module.to_owned();
    while self.get(&module).dfs_index.unwrap() > self.get(&module).dfs_anc_index.unwrap() {
      assert!(!self.get(&module).apm.as_ref().unwrap().is_empty(), "APM for {} is empty", module);
      let next = self.get(&module).apm.as_ref().unwrap()[0].to_owned();
      assert_eq!(self.get(&next).dfs_anc_index, self.get(&module).dfs_anc_index);
      module = next;
      println!("    >> {}", module);
    }
    assert_eq!(self.get(&module).dfs_index, self.get(&module).dfs_anc_index);
    println!("    result={}", module);
    module
  }

  fn inner_module_instantiation(&mut self, name: &str, stack: &mut LoudVec<String>, index: usize) -> usize {
    match &self.get(name).status {
      // Step 2.
      | s @ Status::Instantiating
      | s @ Status::Instantiated
      | s @ Status::EvaluatingAsync
      | s @ Status::Evaluated
      => {
        println!("inner_module_instantiation: short circuit for {} with {:?}", name, s);
        return index;
      },
      // Step 3.
      | Status::Uninstantiated
      => (),
      | s
      => panic!("Wrong status for {}: {:?}", name, s),
    };
    // Step 4.
    self.get_mut(name).set_status(Status::Instantiating);
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
      index = self.inner_module_instantiation(&required, stack, index);
      match &self.get(&required).status {
        | Status::Instantiating
        => {
          assert!(stack.contains(&required));
          let dfs_anc_index = self.get(name).dfs_anc_index.unwrap().min(self.get(&required).dfs_anc_index.unwrap());
          self.get_mut(name).set_anc_index(dfs_anc_index);
        },
        | Status::Instantiated
        | Status::EvaluatingAsync
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
        self.get_mut(&required).set_status(Status::Instantiated);
        done = required == name;
      }
    }
    // Step 14.
    index
  }

  fn instantiate(&mut self, name: &str) {
    assert!(self.get(name).status != Status::Instantiating && self.get(name).status != Status::Evaluating);
    let mut stack = LoudVec::new("Instantiate stack");
    self.inner_module_instantiation(name, &mut stack, 0);
    match self.get(name).status {
      | Status::Instantiated
      | Status::EvaluatingAsync
      | Status::Evaluated
      => (),
      | ref s
      => panic!("Wrong status for {}: {:?}", name, s),
    }
    assert!(stack.is_empty());
  }

  fn fulfilled(&mut self, name: &str) {
    assert!(self.get(name).error.is_none());
    match self.get(name).status {
      | Status::Instantiating
      => {
        assert_eq!(self.get(name).async_, Sync::Sync);
        assert!(self.get(name).apm.as_ref().unwrap().is_empty());
        // XXX possible?
      },
      | Status::EvaluatingAsync
      => {
        self.get_mut(name).set_status(Status::Evaluated);
      },
      | _ => (),
    }
    for m in self.get(name).apm.clone().unwrap() {
      if self.get(name).dfs_index.unwrap() != self.get(name).dfs_anc_index.unwrap() {
        assert_eq!(self.get(&m).dfs_anc_index.unwrap(), self.get(name).dfs_anc_index.unwrap());
      }
      assert!(self.get(&m).pad.unwrap() > 0);
      *self.get_mut(&m).pad.as_mut().unwrap() -= 1;
      if self.get(&m).pad.unwrap() == 0 && self.get(&m).error.is_none() {
        assert_eq!(self.get(&m).status, Status::EvaluatingAsync);
        let root = self.cycle_root(&m);
        if self.get(&root).error.is_some() {
          return;
        }
        self.execute_cyclic_module(&m); // XXX?
      }
    }
    if let Some(promise) = self.get(name).promise.clone() {
      assert_eq!(self.get(name).dfs_index, self.get(name).dfs_anc_index);
      promise.resolve();
    }
  }

  fn rejected(&mut self, name: &str, error: &str) {
    println!("Rejected({})", name);
    assert_eq!(self.get(name).error, None);
    match self.get(name).status {
      | Status::Instantiating
      => {
        assert_eq!(self.get(name).async_, Sync::Sync);
        assert!(self.get(name).apm.as_ref().unwrap().is_empty());
        // XXX possible?
      },
      | Status::EvaluatingAsync
      => {
        self.get_mut(name).set_status(Status::Evaluated);
      },
      | _ => (),
    }
    self.get_mut(name).error = Some(error.to_owned());
    
    for m in self.get(name).apm.clone().unwrap() {
      if self.get(name).dfs_index.unwrap() != self.get(name).dfs_anc_index.unwrap() {
        assert_eq!(self.get(&m).dfs_anc_index.unwrap(), self.get(name).dfs_anc_index.unwrap());
      }
      if self.get(&m).status == Status::EvaluatingAsync {
        self.rejected(&m, error);
      }
    }

    if let Some(promise) = self.get(name).promise.clone() {
      assert_eq!(self.get(name).dfs_index, self.get(name).dfs_anc_index);
      promise.reject(error.to_owned());
    }
  }

  fn execute_cyclic_module(&mut self, name: &str) {
    println!("Execute cyclic module: {}", name);
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
      | Status::EvaluatingAsync
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
      | Status::Instantiated
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
        | Status::EvaluatingAsync
        | Status::Evaluated
        => {
          assert!(!stack.contains(&required));
          self.cycle_root(&required)
        },
        | s
        => panic!("Wrong status for {}: {:?}", required, s),
      };
      match &self.get(&required).error {
        Some(error) => return EvalResult::Error(error.clone()),
        None => (),
      };

      match &self.get(&required).status {
        | Status::EvaluatingAsync
        => {
          *self.get_mut(name).pad.as_mut().unwrap() += 1;
          self.get_mut(&required).apm.as_mut().unwrap().push(name.to_owned());
        },
        | _ => (),
      }
    }

    // Step 14.
    if self.get(&name).pad.unwrap() == 0 {
      self.execute_cyclic_module(name);
      match &self.get(name).error {
        Some(error) => return EvalResult::Error(error.clone()),
        None => (),
      };
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
        // XXX name?
        let status = if self.get(name).async_ == Sync::Async || self.get(name).pad.unwrap() > 0 {
          Status::EvaluatingAsync
        } else {
          Status::Evaluated
        };
        self.get_mut(&required).set_status(status);
        done = required == name;
      }
    }

    // Step 18.
    EvalResult::Index(index)
  }

  fn evaluate(&mut self, name: &str) -> Rc<Promise> {
    let name = match &self.get(name).status {
      | Status::Instantiated
      => name.to_owned(),
      // Step 3.
      | Status::EvaluatingAsync
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
        for (idx, m) in stack.iter().enumerate() {
          assert_eq!(self.get(&m).status, Status::Evaluating);
          self.get_mut(&m).set_status(Status::Evaluated);
          println!("{}", idx);
          if idx + 1 != stack.len() {
            self.rejected(&m, &e);
          }
        }
        assert_eq!(self.get(&name).status, Status::Evaluated);
        assert!(self.get(&name).error.is_some());
        assert_eq!(*self.get(&name).error.as_ref().unwrap(), e);
      },
      // Step 10.
      EvalResult::Index(_) => {
        assert!(self.get(&name).status == Status::Evaluated || self.get(&name).status == Status::EvaluatingAsync);
        assert!(self.get(&name).error.is_none()); // XXX
        assert!(stack.is_empty());
      },
    }

    // Step 11.
    promise
  }
}

fn run(modules: &mut Modules, name: &str) {
  println!(">>> Instantiate");
  modules.instantiate(name);
  for (k, v) in &mut modules.modules {
    println!("Module {}: DFSIndex={:?} DFSAncestorIndex={:?} Async={:?}", k, v.dfs_index, v.dfs_anc_index, v.async_);
    v.dfs_index = None;
    v.dfs_anc_index = None;
  }

  println!(">>> Evaluate");
  modules.evaluate(name);
  println!("=================");
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
}

#[test]
fn example2() {
  println!("Example 2");
  let mut modules = Modules::new();
  modules.insert("A".to_owned(), Sync::Async, vec!["B".to_owned(), "C".to_owned()], false);
  modules.insert("B".to_owned(), Sync::Async, vec!["A".to_owned()], false);
  modules.insert("C".to_owned(), Sync::Sync, vec![], false);
  run(&mut modules, "A");
}

#[test]
fn example3() {
  println!("Example 3");
  let mut modules = Modules::new();
  modules.insert("B".to_owned(), Sync::Sync, vec![], true);
  run(&mut modules, "B");
  for (k, v) in &modules.modules {
    println!("Module {}: status is {:?}", k, v.status);
  }
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
  for (k, v) in &modules.modules {
    println!("Module {}: status is {:?}", k, v.status);
  }
  modules.evaluate("B");
//  modules.evaluate("C");
//  modules.evaluate("D");
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
  for (k, v) in &modules.modules {
    println!("Module {}: Status={:?} DFSIndex={:?} DFSAncestorIndex={:?} Async={:?}", k, v.status, v.dfs_index, v.dfs_anc_index, v.async_);
  }
  assert_eq!(modules.execution_order, &[
    "D".to_owned(),
    "B".to_owned(),
    "E".to_owned(),
    "C".to_owned(),
    "A".to_owned(),
  ]);
}

fn main() {
}
