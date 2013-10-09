/*
	Title: Modelling cross origin requests and preventing them with CORP
	Author: Krishna Chaitanya T
	Date: 1st March, 2013

	Description: The predicates in this model show instances of attacker's capabilities. 
	By leveraging cross origin request vectors (img, form etc), an attacker can cause a change in 
	the state of any server.	The basic browser model (without CORP policydata) shows instances 
	where an attacker's web page can make cross origin calls to a genuine site. On configuring 
	CORP, the model shows how permissions on cross origin calls are enforced.
*/

//An abstract signature has no elements except those belonging to its extensions
abstract sig Path{}
abstract sig ContentPath, WebPagesPath extends Path{}
sig ImgPath, JsPath, CssPath extends ContentPath{}
sig NonSensitivePagesPath, SensitivePagesPath extends WebPagesPath{}

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
	reqPath: one Path,
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
	activeDoc: Document,
	policyData: set CORP
}

abstract sig Server extends NetworkEndPoint{
	resourcePath: set Path
}

sig EvilServer, GenuineServer extends Server{}

sig Document{
	docOrigin: Origin,
	elements: set HTMLElement
}

/****************************
				PERMISSION
****************************/

abstract sig Permission {}
sig Deny extends Permission {}

abstract sig CORP{
	policyType: ActiveHTMLElement,
	policyPermission: Path + Permission 
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
	htmlTransactions: lone HTTPTransaction
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

/*When a HTTP request is made to a server, the following hold good:
	1. If the response type is IMAGE_TYPE, then the server should contain an image resource.
		 i.e., some (ImgPath & server.resourcePath)
	2. The request path should point to server.resouce path. i.e., (some reqPath & server.resourcePath)
	The above two conditions can be written as: some (ImgPath & server.resourcePath & reqPath) 
*/
fact ServerSetsContentType{
	all t:HTTPTransaction | let contentType=t.resp.respHeader.contentType, server=t.resp.from,  reqPath=t.req.reqPath | {
		#server.resourcePath>1
		contentType= IMAGE_TYPE => some (ImgPath & server.resourcePath & reqPath) 
		contentType= CSS_TYPE => some (CssPath & server.resourcePath & reqPath)
		contentType= SCRIPT_TYPE => some (JsPath & server.resourcePath & reqPath)
		contentType= HTML_TYPE => some (WebPagesPath & server.resourcePath & reqPath)
	}
}

fact StateChangeRules{
	all t:HTTPTransaction | {	
		t.req.canChangeState=TRUE => some (t.req.reqPath & SensitivePagesPath)
		t.req.canChangeState=FALSE => no SensitivePagesPath
	}
}

/* Our modified browser looks at policyType set by CORP and 
	applies it to the corresponding 'type' of HTML element. */
fact CORP_Enforcement{
	some CORP implies {
	//	ConfigureCORP[1]

		/*
		let policyType=Browser.policyData.policyType|{		
			//CORP is configured on the server such that the type of CORP.policyType matches with contentType of URL
			e.g., CORP:  {	img: "http://A.com/img", script: "http://A.com/js" }
			Here, CORP.policyType refers to the key (e.g., img, script etc.)
			
			In the browser, the type of element which makes a request is matched with CORP's policyType.
				e.g., If <img src="http://A.com/.."> makes a request, policyType is set to Image_Type.
				The browser then checks the corresponding URL for Image_Type from CORP header (see above) 
				and allows/denies it based on the restriction.
		}
		*/
	/*	some  HTTPTransaction => {
			//setting CORP.policyType to ActiveHTMLElement
			Browser.policyData.policyType=htmlTransactions.HTTPTransaction
		}*/
		
		let policyPermission=CORP.policyPermission, elemTrans=ActiveHTMLElement.htmlTransactions| {
			//Global fact: No X-origin state changes allowed when CORP is configured.
			elemTrans.req.canChangeState=FALSE

			//Global fact: Accept-type and content-type must match when CORP is configured.
			elemTrans.resp.respHeader.contentType= elemTrans.req.reqHeader.acceptType

			policyPermission = NonSensitivePagesPath=> {
				elemTrans.req.reqPath = NonSensitivePagesPath
			}

			policyPermission = ImgPath=> {
				elemTrans.req.reqPath = ImgPath
			}
			
			policyPermission = JsPath=> {
				elemTrans.req.reqPath = JsPath
			}

			policyPermission = CssPath=> {
				elemTrans.req.reqPath = CssPath
			}

			policyPermission = Deny => {
				// Block HTTP transactions from the element on which CORP is applied.
				no CORP.policyType.htmlTransactions 
				// Ensure that other ActiveHTMLelements which do not make HTTP transactions by design of
				// this browser model do not show up in the instance. This is a hack only to remove confusion.
				noIdleElementsInCORP
			}
		}
	}
}

fact noOrphanElements{
// Ensures no unrelated/hanging elements exist
	no (HTMLElement - Browser.activeDoc.elements)
	//no (Data - Server.hasData)
	no (Document - Browser.activeDoc)

	no (Server - Origin.pointsTo)

	no ContentTypeToken - (ContentTypeHeader.contentType + AcceptHeader.acceptType)

	no (ContentTypeHeader - HTTPTransaction.resp.respHeader) 
	no (AcceptHeader - HTTPTransaction.req.reqHeader)

	no (Permission - CORP.policyPermission)
	all pd: CORP | pd in Browser.policyData

	no (Path - (Server.resourcePath + HTTPRequest.reqPath))

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
	//no disj o1,o2 : Origin | (not sameOrigin[o1,o2]) and o1.dnsLabel = o2.dnsLabel

	all disj e1, e2: ActiveHTMLElement | no (e1.htmlTransactions & e2.htmlTransactions)
	
	all disj s1, s2: Server | no (s1.resourcePath & s2.resourcePath)
}

/****************************
					PREDICATES
****************************/

/*
	pred noIdleElements:: As per the signature "sig ActiveHTMLElement {htmlTransactions: lone HTTPTransaction}", there can be
	ActiveHTMLElement which do not make HTTP transactions. This predicate disables such elements temporarily.
*/
pred noIdleElements{
	no (ActiveHTMLElement - htmlTransactions.HTTPTransaction)
}

pred noIdleElementsInCORP{
	no (ActiveHTMLElement-CORP.policyType) - htmlTransactions.HTTPTransaction
}

pred showBasicModel{
	#Browser = 1
	#Server = 1
	#HTTPTransaction = 0
	#ContentTypeHeader =0
	#AcceptHeader=0
	#ContentTypeToken=0
	#Path=0
	no Browser.activeDoc.elements
	ConfigureCORP[0]
}

pred showOneTransaction{
	#Browser = 1
	#Server = 1
	#HTTPTransaction = 1
	ConfigureCORP[0]
	noIdleElements
}

//If an image is fetched by a HTTP Transaction, it should return content only of Image content type. 
//Else it could be a malicious request.
pred wrongResponseTypePossible {
	some elem:LoadingElement, t:HTTPTransaction
	{
		elem.htmlTransactions.req=t.req
		elem.htmlTransactions.resp=t.resp
		no (elem.htmlTransactions.req.reqHeader.acceptType & 
				elem.htmlTransactions.resp.respHeader.contentType)
	}
	ConfigureCORP[0]
	noIdleElements
}

pred ElementCanChangeState {
	some elem:ActiveHTMLElement, t:HTTPTransaction{
		elem.htmlTransactions.req=t.req
		elem.htmlTransactions.resp=t.resp
		t.req.canChangeState=TRUE
	}
	ConfigureCORP[0]
	noIdleElements
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
		//elem.htmlTransactions.req.reqHeader.acceptType=type 
	}
	#Browser = 1
	#Server = 2
	#Browser.policyData= 0
	#HTTPTransaction =1
	noIdleElements
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
	#CORP=0
	noIdleElements

	HTTPTransaction.req.canChangeState=FALSE
	no (Server & EvilServer)
}	

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
	ConfigureCORP[0]
	noIdleElements
	HTTPTransaction.req.canChangeState=TRUE
}

pred ConfigureCORP[num: Int]{
	#CORP = num
}

pred loadingElementWithCORP{
	some elem: LoadingElement | {
		elem.elementOrigin.pointsTo=EvilServer
		elem.htmlTransactions.req.to=GenuineServer
	}

	ConfigureCORP[1]
	CORP.policyPermission=ContentPath
	noIdleElements
	#Browser = 1
	#Server = 2
	#HTTPTransaction =1
}

pred actionElementWithCORP{
	some elem: ActionElement | {
		elem.elementOrigin.pointsTo=EvilServer
		elem.htmlTransactions.req.to=GenuineServer
	}

	ConfigureCORP[1]
	CORP.policyPermission=NonSensitivePagesPath
	noIdleElements
	#Browser = 1
	#Server = 2
	#HTTPTransaction =1
}


pred XOriginStateChangeWithCORP{
	XOriginTransaction
	some elem:ActiveHTMLElement | elem.htmlTransactions.req.canChangeState=TRUE
	ConfigureCORP[1]
}

assert wrongResponseTypeWithCORP{
	no elem:ActiveHTMLElement, t:HTTPTransaction
	{
		elem.htmlTransactions = t
		no (elem.htmlTransactions.req.reqHeader.acceptType & 
				elem.htmlTransactions.resp.respHeader.contentType)
		ConfigureCORP[1]
	}
}
// This predicate is same as "maliciousXOriginTransaction", except that ConfigureCORP is set to 1
pred maliciousXOriginTransactionWithCORP{
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
	ConfigureCORP[1]
	noIdleElements
	HTTPTransaction.req.canChangeState=TRUE
}

pred NoFramingAttacks{
	ConfigureCORP[1]
	no HTMLElement - Iframe
	CORP.policyType=Iframe
	Iframe.elementOrigin.pointsTo=EvilServer
	CORP.policyPermission=Deny
}


assert NoFramingAttacks{
	all ifr:Iframe, t:HTTPTransaction | {
		ConfigureCORP[1]
		CORP.policyType=ifr
		CORP.policyPermission=Deny
		no HTMLElement - ifr
		ifr.elementOrigin.pointsTo=EvilServer
	} implies no t
}

check NoFramingAttacks for 20
run showBasicModel
run showOneTransaction

run wrongResponseTypePossible
run loadingElementCanChangeState
run actionElementsCanChangeState
run almostSafeXOriginTransaction 
run maliciousXOriginTransaction 

run loadingElementWithCORP
run actionElementWithCORP //for 5 but exactly 2 Browser, exactly 2 Server, exactly 2 HTTPTransaction
run XOriginStateChangeWithCORP for 20 expect 0 // Holds good even for scope 20 (10-08-2013)
run maliciousXOriginTransactionWithCORP for 10 expect 0
check wrongResponseTypeWithCORP for 10 expect 0// Holds good even for scope 20 (10-08-2013)

run NoFramingAttacks

/*TODO: 
	>> Should we remove the predicate noIdleElements?
	>> If yes, replace "lone" with "one" below.
	abstract sig ActiveHTMLElement extends HTMLElement {
		htmlTransactions: lone HTTPTransaction 
	}
*/
