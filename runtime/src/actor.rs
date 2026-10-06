use crate::fiber::Fiber;
use crate::ids::ActorId;
use crate::mpsc::MpscQueue;
use crate::value::MessagePayload;

/// The lifecycle position of an [`Actor`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ActorState {
    /// Created but not yet begun processing messages.
    Starting,
    /// Actively processing messages.
    Running,
    /// Temporarily halted.
    Suspended,
    /// Shut down cleanly.
    Stopped,
    /// Terminated because its handler panicked.
    Failed,
}

/// How a supervisor reacts when one of its children fails.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SupervisionStrategy {
    /// Restart only the failing child, leaving its siblings untouched.
    OneForOne,
    /// Restart every child of the supervisor.
    OneForAll,
}

/// A message delivered to an actor's mailbox.
#[derive(Debug, Clone)]
pub struct ActorMessage {
    /// The actor that sent the message.
    pub sender: ActorId,
    /// The message name, used to select a handler.
    pub tag: String,
    /// The message body: either data or a control signal.
    pub payload: MessagePayload,
}

impl ActorMessage {
    /// Builds a message from `sender` with the given tag and payload.
    pub fn new(sender: ActorId, tag: &str, payload: MessagePayload) -> Self {
        ActorMessage {
            sender,
            tag: tag.to_string(),
            payload,
        }
    }
}

/// An actor: a mailbox, the [`Fiber`] running its handler, and its supervision
/// metadata.
///
/// Messages are queued through an [`MpscQueue`], so [`Actor::send`] may be
/// called from any thread.
pub struct Actor {
    id: ActorId,
    state: ActorState,
    mailbox: MpscQueue<ActorMessage>,
    fiber: Option<Fiber>,
    supervisor: Option<ActorId>,
    strategy: SupervisionStrategy,
}

impl Actor {
    /// Creates a starting actor whose handler runs on `fiber`.
    pub fn new(fiber: Fiber) -> Self {
        Actor {
            id: ActorId::new(),
            state: ActorState::Starting,
            mailbox: MpscQueue::new(),
            fiber: Some(fiber),
            supervisor: None,
            strategy: SupervisionStrategy::OneForOne,
        }
    }

    /// Returns the actor's id.
    pub fn id(&self) -> ActorId {
        self.id
    }

    /// Returns the actor's current state.
    pub fn state(&self) -> ActorState {
        self.state
    }

    /// Records a new state for this actor.
    pub fn set_state(&mut self, state: ActorState) {
        self.state = state;
    }

    /// Enqueues `msg` in the actor's mailbox.
    pub fn send(&self, msg: ActorMessage) {
        self.mailbox.push(msg);
    }

    /// Takes the next message from the mailbox, or `None` if it is empty.
    pub fn receive(&self) -> Option<ActorMessage> {
        self.mailbox.pop()
    }

    /// Returns the number of queued messages.
    pub fn mailbox_len(&self) -> usize {
        self.mailbox.len()
    }

    /// Returns a clone of the mailbox handle for sending from elsewhere.
    pub fn mailbox(&self) -> MpscQueue<ActorMessage> {
        self.mailbox.clone()
    }

    /// Discards every queued message.
    pub fn clear_mailbox(&self) {
        self.mailbox.clear();
    }

    /// Sets the actor that supervises this one.
    pub fn set_supervisor(&mut self, supervisor: ActorId) {
        self.supervisor = Some(supervisor);
    }

    /// Returns the supervising actor, or `None` if this actor is unsupervised.
    pub fn supervisor(&self) -> Option<ActorId> {
        self.supervisor
    }

    /// Sets the strategy used when this actor's children fail.
    pub fn set_strategy(&mut self, strategy: SupervisionStrategy) {
        self.strategy = strategy;
    }

    /// Returns the current supervision strategy.
    pub fn strategy(&self) -> SupervisionStrategy {
        self.strategy
    }

    /// Borrows the fiber running this actor's handler, if one is attached.
    pub fn fiber(&self) -> Option<&Fiber> {
        self.fiber.as_ref()
    }

    /// Mutably borrows the fiber, if one is attached.
    pub fn fiber_mut(&mut self) -> Option<&mut Fiber> {
        self.fiber.as_mut()
    }

    /// Detaches and returns the fiber, leaving the actor with none.
    pub fn take_fiber(&mut self) -> Option<Fiber> {
        self.fiber.take()
    }
}

impl std::fmt::Debug for Actor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Actor")
            .field("id", &self.id)
            .field("state", &self.state)
            .field("supervisor", &self.supervisor)
            .field("strategy", &self.strategy)
            .field("mailbox_len", &self.mailbox.len())
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fiber::FiberYield;
    use crate::value::MorphValue;

    fn make_test_fiber() -> Fiber {
        Fiber::new(|_ctx| FiberYield::Complete(Ok(())))
    }

    #[test]
    fn test_actor_send_receive() {
        let actor = Actor::new(make_test_fiber());
        let id = actor.id();
        actor.send(ActorMessage::new(
            id,
            "ping",
            MessagePayload::Value(MorphValue::Int32(42)),
        ));
        actor.send(ActorMessage::new(
            id,
            "pong",
            MessagePayload::Value(MorphValue::Bool(true)),
        ));
        assert_eq!(actor.mailbox_len(), 2);
        let msg1 = actor.receive().unwrap();
        assert_eq!(msg1.tag, "ping");
        assert_eq!(msg1.sender, id);
        let msg2 = actor.receive().unwrap();
        assert_eq!(msg2.tag, "pong");
        assert!(actor.receive().is_none());
    }

    #[test]
    fn test_actor_supervision() {
        let mut actor = Actor::new(make_test_fiber());
        let supervisor = ActorId::new();
        assert!(actor.supervisor().is_none());
        actor.set_supervisor(supervisor);
        assert_eq!(actor.supervisor(), Some(supervisor));
    }

    #[test]
    fn test_actor_state_transitions() {
        let mut actor = Actor::new(make_test_fiber());
        assert_eq!(actor.state(), ActorState::Starting);
        actor.set_state(ActorState::Running);
        assert_eq!(actor.state(), ActorState::Running);
        actor.set_state(ActorState::Stopped);
        assert_eq!(actor.state(), ActorState::Stopped);
    }

    #[test]
    fn test_actor_take_fiber() {
        let mut actor = Actor::new(make_test_fiber());
        assert!(actor.fiber().is_some());
        let fiber = actor.take_fiber();
        assert!(fiber.is_some());
        assert!(actor.fiber().is_none());
        assert!(actor.take_fiber().is_none());
    }
}
