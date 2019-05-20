use std::collections::HashMap;
use std::rc::Rc;
use std::cell::RefCell;
use std::fmt::Debug;

struct LoudVec<T>(Vec<T>);

impl<T: Debug> LoudVec<T> {
  fn new() -> Self {
    Self(vec![])
  }
  fn push(&mut self, value: T) {
    println!("Push {:?}", value);
    self.0.push(value)
  }
  fn pop(&mut self) -> Option<T> {
    let value = self.0.pop();
    println!("Pop {:?}", value);
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

struct Promise(RefCell<Option<Result<(), String>>>);

impl Promise {
  fn new() -> Rc<Self> {
    Rc::new(Self(RefCell::new(None)))
  }
  fn resolve(&self) {
    let mut cell = self.0.borrow_mut();
    assert_eq!(*cell, None);
    *cell = Some(Ok(()));
  }
  fn reject(&self, error: String) {
    let mut cell = self.0.borrow_mut();
    assert_eq!(*cell, None);
    *cell = Some(Err(error));
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
  Evaluated,
}

struct Module {
  name: String,
  status: Status,
  async_: Sync,
  module_async: Sync,
  requested: Vec<String>,
  dfs_index : Option<usize>,
  dfs_anc_index: Option<usize>,
  error: Option<String>,
  broken: bool,
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
      status: Status::Uninstantiated,
      async_,
      module_async: async_,
      requested,
      dfs_index: None,
      dfs_anc_index: None,
      error: None,
      broken,
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

  fn execute_module_sync(&mut self) -> Result<(), String> {
    println!("execute_module_sync: {}", self.name);
    assert_eq!(self.module_async, Sync::Sync);
    if self.broken {
      Err(format!("Module {} failed sync", self.name))
    } else {
      Ok(())
    }
  }
  fn execute_module_async(&mut self, capability: Rc<Promise>) {
    println!("execute_module_async: {}", self.name);
    assert_eq!(self.module_async, Sync::Async);
    if self.broken {
      capability.reject(format!("Module {} failed async", self.name));
    } else {
      capability.resolve();
    }
  }
}

struct Modules {
  modules: HashMap<String, Module>,
}

impl Modules {
  fn new() -> Self {
    Modules {
      modules: HashMap::new(),
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

  fn inner_module_instantiation(&mut self, name: &str, stack: &mut LoudVec<String>, index: usize) -> usize {
    match &self.get(name).status {
      // Step 2.
      | s @ Status::Instantiating
      | s @ Status::Instantiated
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
    let mut stack = LoudVec::new();
    self.inner_module_instantiation(name, &mut stack, 0);
    assert!(self.get(name).status == Status::Instantiated || self.get(name).status == Status::Evaluated);
    assert!(stack.is_empty());
  }

  fn execute_module_when_imports_ready(&mut self, name: &str, promises: Vec<Rc<Promise>>, cap: Rc<Promise>) {
    println!("execute_module_when_imports_ready({}, [..{}])", name, promises.len());
    if promises.is_empty() {
      assert_eq!(self.get(name).module_async, Sync::Async);
      self.get_mut(name).execute_module_async(cap);
      return;
    }
    for promise in promises {
      println!("  >> {:?}", *promise.0.borrow());
      match *promise.0.borrow() {
        None => panic!(),
        Some(Ok(())) => (),
        Some(Err(ref e)) => {
          cap.reject(e.clone());
          return;
        }
      }
    }
    if self.get(name).module_async == Sync::Async {
      self.get_mut(name).execute_module_async(cap);
    } else {
      let result = self.get_mut(name).execute_module_sync();
      match result {
        Ok(()) => cap.resolve(),
        Err(e) => cap.reject(e),
      }
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
    let mut index = index + 1;
    // Step 9.
    stack.push(name.to_owned());
    // Step 10.
    let mut async_deps = vec![];
    
    // Step 11.
    for required in self.get(name).requested.clone() {
      index = match self.inner_module_evaluation(&required, stack, index) {
        EvalResult::Error(error) => return EvalResult::Error(error),
        EvalResult::Index(index) => index,
      };

      match &self.get(&required).status {
        | Status::Evaluating
        => {
          assert!(stack.contains(&required));
          let dfs_anc_index = self.get(name).dfs_anc_index.unwrap().min(self.get(&required).dfs_anc_index.unwrap());
          println!("Setting [[DFSAncestorIndex]] for {} from {} to {}", name, self.get(name).dfs_anc_index.unwrap(), dfs_anc_index);
          self.get_mut(name).set_anc_index(dfs_anc_index);
        },
        | Status::Evaluated
        => {
          assert!(!stack.contains(&required));
          if self.get(&required).async_ == Sync::Async {
            assert!(self.get(&name).async_ == Sync::Async);
            async_deps.push(self.get(&required).promise.as_ref().unwrap().clone());
          }
        },
        | s
        => panic!("Wrong status for {}: {:?}", required, s),
      };
    }

    // Step 12.
    if self.get(&name).async_ == Sync::Sync {
      match self.get_mut(&name).execute_module_sync() {
        Ok(()) => (),
        Err(e) => return EvalResult::Error(e),
      }
    // Step 13.
    } else {
      let promise = Promise::new();
      self.get_mut(name).promise = Some(promise.clone());
      self.execute_module_when_imports_ready(name, async_deps, promise);
    }

    // Step 14.
    assert_eq!(stack.iter().filter(|s| **s == name).count(), 1);
    // Step 15.
    assert!(self.get(name).dfs_anc_index.unwrap() <=
            self.get(name).dfs_index.unwrap());
    // Step 16.
    if self.get(name).dfs_anc_index.unwrap() == self.get(name).dfs_index.unwrap() {
      let mut done = false;
      while !done {
        let required = stack.pop().unwrap();
        self.get_mut(&required).set_status(Status::Evaluated);
        done = required == name;
        if !done && self.get(&name).async_ == Sync::Async {
          self.get_mut(&required).promise = self.get(&name).promise.clone();
        }
      }
    }

    // Step 17.
    EvalResult::Index(index)
  }

  fn evaluate(&mut self, name: &str) {
    match &self.get(name).status {
      | Status::Instantiated
      | Status::Evaluated
      => (),
      | s
      => panic!("Wrong status for {}: {:?}", name, s),
    }
    let mut stack = LoudVec::new();
    let result = self.inner_module_evaluation(name, &mut stack, 0);
    println!("Result for {}: {:?}", name, result);
    let mut error_case = false;
    match result {
      EvalResult::Error(e) => {
        for m in stack.iter().rev() {
          assert!(self.get(&m).status == Status::Evaluating);
          if self.get(&m).async_ == Sync::Async {
            println!(" >>>> error case {} <<<< ", m);
            error_case = true;
            return;
          }
          self.get_mut(&m).set_status(Status::Evaluated);
          self.get_mut(&m).error = Some(e.clone());
        }
        assert!(self.get(name).status == Status::Evaluated);
        assert!(self.get(name).error.is_some());
        assert_eq!(*self.get(name).error.as_ref().unwrap(), e);
      },
      EvalResult::Index(_) => {
        assert!(self.get(name).status == Status::Evaluated);
        assert!(self.get(name).error.is_none());
        assert!(stack.is_empty());
        // If module.[[Async]] is true, return module.[[EvaluationPromise]].
        // Otherwise, return undefined.       
      },
    }
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

fn example2() {
  println!("Example 2");
  let mut modules = Modules::new();
  modules.insert("A".to_owned(), Sync::Async, vec!["B".to_owned(), "C".to_owned()], false);
  modules.insert("B".to_owned(), Sync::Async, vec!["A".to_owned()], false);
  modules.insert("C".to_owned(), Sync::Sync, vec![], false);
  run(&mut modules, "A");
}

fn example3() {
  println!("Example 3");
  let mut modules = Modules::new();
//  modules.insert("A".to_owned(), Sync::Async, vec!["B".to_owned(), "C".to_owned(), "D".to_owned()], false);
//  modules.insert("A".to_owned(), Sync::Async, vec!["B".to_owned()], false);
  modules.insert("B".to_owned(), Sync::Async, vec!["C".to_owned()], false);
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

fn main() {
  println!("Hello, world!");
  example1();
  example2();
  example3();
}
