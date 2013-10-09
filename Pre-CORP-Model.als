/*
	Title: Modelling cross origin requests and preventing them with CORP
	Author: Krishna Chaitanya T
	Date: 1st March, 2013

	Description: The predicates in this model show instances of attacker's capabilities. 
	By leveraging cross origin request vectors (img, form etc), an attacker can cause a change in 
	the state of any server.	The basic browser model shows instances 
	where an attacker's web page can make cross origin calls to a genuine site. On configuring 
	CORP, the model shows how permissions on cross origin calls are enforced.
*/

//An abstract signature has no elements except those belonging to its extensions

abstract sig Bool{}
sig TRUE, FALSE extends Bool{}


/****************************
				HTTP TRANSACTION
****************************/
abstract sig Event{}
abstract sig HTTPEvent extends Event { 
	host : Origin 
}

abstract sig HTTPTransaction{
	req:  one HTTPRequest,
	resp: one HTTPResponse
}

sig HTTPRequest extends HTTPEvent{
	from: one Browser,
	to: one Server,
	reqHeader: HTTPRequestHeader,
	canChangeState: one Bool
} 

sig HTTPResponse extends HTTPEvent{
	from: one Server,
	to: one Browser,
	respHeader: HTTPResponseHeader
}

abstract sig HTTPRequestHeader{}
sig AcceptHeader extends HTTPRequestHeader {acceptType: ContentTypeToken}

abstract sig HTTPResponseHeader{}
sig ContentTypeHeader extends HTTPResponseHeader {contentType: ContentTypeToken}

/****************************
				END POINTS
****************************/

sig Origin{
	pointsTo: one Server
}

abstract sig NetworkEndPoint{}

sig Browser extends NetworkEndPoint{
	activeDoc: Document
}

abstract sig Server extends NetworkEndPoint{}

sig EvilServer, GenuineServer extends Server{}

sig Document{
	docOrigin: Origin,
	elements: set HTMLElement
}

/****************************
					ELEMENTS
****************************/

//Network capable elements: IFrame, Image, Link, Script, Anchor, Embed, Object, Applet
sig HTMLElement{}

sig PassiveHTMLElement extends HTMLElement {}
sig  Div, Span, Textbox extends PassiveHTMLElement{}

abstract sig ActiveHTMLElement extends HTMLElement {
	elementOrigin: Origin,
	htmlTransactions: one HTTPTransaction
}

abstract sig LoadingElement, ActionElement extends ActiveHTMLElement {}
sig ScriptElement, ImageElement, CssElement, Iframe extends LoadingElement {}
sig Hyperlink, Form extends ActionElement{}

abstract sig ContentTypeToken{}
sig IMAGE_TYPE, CSS_TYPE, SCRIPT_TYPE, HTML_TYPE extends ContentTypeToken{}
//AUDIO_TYPE, VIDEO_TYPE extends ContentTypeToken{}


/****************************
		 					FACTS
****************************/

fact TransactionRules{
	all t:HTTPTransaction, b:Browser, s:Server| {
		//Request and response must belong to the same origin
		t.req.host = t.resp.host
		//A Http request's hostname and its destination server's origin must be the same
			/*pointsTo=(Origin, Server).  
				t.req.to.~pointsTo= (t.req.to).(Server, Origin) -> (Server. (Server, Origin)) -> Origin */
		t.req.host = t.req.to.~pointsTo 

		//If a request is sent to a server, response should be received from the same server 
		s=t.req.to => s = t.resp.from 
		//If a request is sent from a browser, response should be received by the same browser
		b = t.req.from => b = t.resp.to 
	}

	// Two transactions should not interfere with each other's request/response
	all disj t1,t2: HTTPTransaction | {
		no (t1.req & t2.req) 
		no (t1.resp & t2.resp) 	
	}
	//All HTTPTransactions should be due to some elements
	HTTPTransaction in ActiveHTMLElement.htmlTransactions
}


//Fact:: Elements inherit parent document's origin
fact ElementsInheritParentOrigin{
	all elem:HTMLElement | elem.~elements.docOrigin = elem.elementOrigin
}

//Browsers set AcceptType header correctly.
// e.g., If an <img> makes a HTTP request, browsers set acceptHeader to "img/*"

fact BrowserSetsAcceptType{
	all t:HTTPTransaction | let acceptType=t.req.reqHeader.acceptType |{
		some ImageElement => acceptType = IMAGE_TYPE
		some CssElement => acceptType = CSS_TYPE
		some ScriptElement => acceptType = SCRIPT_TYPE 

		some Iframe => acceptType = HTML_TYPE
		some Hyperlink => acceptType = HTML_TYPE 
		some Form => acceptType = HTML_TYPE
	}
}

fact noOrphanElements{
// Ensures no unrelated/hanging elements exist
	no (HTMLElement - Browser.activeDoc.elements)
	//no (Data - Server.hasData)
	no (Document - Browser.activeDoc)
	//no (Token - Browser.activeDoc.elements.hasData)
	no (Server - Origin.pointsTo)

	no ContentTypeToken - (ContentTypeHeader.contentType + AcceptHeader.acceptType)

	no (ContentTypeHeader - HTTPTransaction.resp.respHeader) 
	no (AcceptHeader - HTTPTransaction.req.reqHeader)

	//No orphan Request/Responses. 
	(no HTTPRequest-HTTPTransaction.req) and (no HTTPResponse-HTTPTransaction.resp)

	no Origin - (HTTPRequest.host + HTTPResponse.host+Document.docOrigin)

	all b:Bool | b in HTTPRequest.canChangeState
}

fact Disjointness {
	all disj b1,b2: Browser | {
		no (b1.activeDoc & b2.activeDoc)
		no (b1.activeDoc.docOrigin & b2.activeDoc.docOrigin)
	}
	//Two distinct origins do not point to the same server
	all disj o1,o2:Origin | no (o1.pointsTo & o2.pointsTo)

	all disj e1, e2: ActiveHTMLElement | no (e1.htmlTransactions & e2.htmlTransactions)
}

/****************************
					PREDICATES
****************************/

pred showBasicModel{
	#Browser = 1
	#Server = 1
	#HTTPTransaction = 0
	#ContentTypeHeader =0
	#AcceptHeader=0
	#ContentTypeToken=0
	no Browser.activeDoc.elements
}

pred showOneTransaction{
	#Browser = 1
	#Server = 1
	#HTTPTransaction = 1
}

//If an image is fetched by a HTTP Transaction, it should return content only of Image content type. 
//Else it could be a malicious request.
pred wrongResponseTypePossible {
	some elem:LoadingElement
	{
		no (elem.htmlTransactions.req.reqHeader.acceptType & 
				elem.htmlTransactions.resp.respHeader.contentType)
	}
}

pred ElementCanChangeState {
	some elem:ActiveHTMLElement {
		elem.htmlTransactions.req.canChangeState=TRUE
	}
}
pred loadingElementCanChangeState {
	ElementCanChangeState
	some (ActiveHTMLElement - ActionElement)
}

pred actionElementsCanChangeState{
	ElementCanChangeState
	some (ActiveHTMLElement - LoadingElement)
}


/*
 //Active HTML elements like images, iframes etc can always load from remote origins.
elements: (DOM, Element)
*/
pred XOriginTransaction{
	some disj o1, o2: Origin, elem:ActiveHTMLElement|{
		elem.~elements.docOrigin=o1
		elem.htmlTransactions.req.host=o2
	}
	#Browser = 1
	#Server = 2
	#HTTPTransaction =1
}	

//Includes genuine GET as well as cross-site timing attacks
pred almostSafeXOriginTransaction{
	some disj o1, o2: Origin,  elem:ActiveHTMLElement|{
		elem.~elements.docOrigin=o1
		elem.htmlTransactions.req.host=o2
	}
	#Browser = 1
	#Server = 2
	#HTTPTransaction =1

	HTTPTransaction.req.canChangeState=FALSE
	no (Server & EvilServer)
}	

//Includes CSRF, Clickjacking
pred maliciousXOriginTransaction{
	some disj o1, o2: Origin, elem:ActiveHTMLElement| let elemTrans=elem.htmlTransactions | {
		elem.~elements.docOrigin=o1
		elemTrans.req.host=o2
		elem.elementOrigin.pointsTo=EvilServer
		elemTrans.req.to=GenuineServer
		no (elemTrans.req.reqHeader.acceptType & 
				elemTrans.resp.respHeader.contentType)
	}
	#Browser = 1
	#Server = 2
	#HTTPTransaction =1

	HTTPTransaction.req.canChangeState=TRUE
}

run showBasicModel
run showOneTransaction
run wrongResponseTypePossible
run loadingElementCanChangeState
run actionElementsCanChangeState
run almostSafeXOriginTransaction 
run maliciousXOriginTransaction 
