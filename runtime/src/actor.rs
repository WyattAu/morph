use crate::fiber::Fiber;
use crate::ids::ActorId;
use crate::mpsc::MpscQueue;
use crate::value::MessagePayload;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ActorState {
    Starting,
    Running,
    Suspended,
    Stopped,
    Failed,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SupervisionStrategy {
    OneForOne,
    OneForAll,
}

#[derive(Debug, Clone)]
pub struct ActorMessage {
    pub sender: ActorId,
    pub tag: String,
    pub payload: MessagePayload,
}

impl ActorMessage {
    pub fn new(sender: ActorId, tag: &str, payload: MessagePayload) -> Self {
        ActorMessage {
            sender,
            tag: tag.to_string(),
            payload,
        }
    }
}

pub struct Actor {
    id: ActorId,
    state: ActorState,
    mailbox: MpscQueue<ActorMessage>,
    fiber: Option<Fiber>,
    supervisor: Option<ActorId>,
    strategy: SupervisionStrategy,
}

impl Actor {
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

    pub fn id(&self) -> ActorId {
        self.id
    }

    pub fn state(&self) -> ActorState {
        self.state
    }

    pub fn set_state(&mut self, state: ActorState) {
        self.state = state;
    }

    pub fn send(&self, msg: ActorMessage) {
        self.mailbox.push(msg);
    }

    pub fn receive(&self) -> Option<ActorMessage> {
        self.mailbox.pop()
    }

    pub fn mailbox_len(&self) -> usize {
        self.mailbox.len()
    }

    pub fn mailbox(&self) -> MpscQueue<ActorMessage> {
        self.mailbox.clone()
    }

    pub fn clear_mailbox(&self) {
        self.mailbox.clear();
    }

    pub fn set_supervisor(&mut self, supervisor: ActorId) {
        self.supervisor = Some(supervisor);
    }

    pub fn supervisor(&self) -> Option<ActorId> {
        self.supervisor
    }

    pub fn set_strategy(&mut self, strategy: SupervisionStrategy) {
        self.strategy = strategy;
    }

    pub fn strategy(&self) -> SupervisionStrategy {
        self.strategy
    }

    pub fn fiber(&self) -> Option<&Fiber> {
        self.fiber.as_ref()
    }

    pub fn fiber_mut(&mut self) -> Option<&mut Fiber> {
        self.fiber.as_mut()
    }

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
